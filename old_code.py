# -*- coding: utf-8 -*-

# SPDX-License-Identifier: MIT
# Copyright © 2021 André Santos

StrategyP = namedtuple("P", ("strategy", "spam"))
StrategyQ = namedtuple("Q", ("strategy", "spam", "min_time"))
StrategyA = namedtuple("A", ("strategy", "spam", "min_num", "max_num"))
StrategyB = namedtuple("B", ("spam", "timeout"))

Strategies = namedtuple("Strategies", ("p", "q", "a", "b"))


# publisher stages:
#   - stage 1 [1+ chunks]: up to activator (if not launch)
#   - stage 2 [1+ chunks]: up to trigger
#   - stage 3 [0+ chunks]: after trigger

# 'globally' and 'until' do not have stage 1
# only 'requires', 'causes' and 'forbids' have stage 2

class StrategyManager(object):
    __slots__ = ("stage1", "stage2", "stage3", "terminator", "deadline", "min_times")

    def __init__(self, pubs, assumptions, data_axioms, time_axioms, deadline=10.0):
        # pubs: topic -> ROS type token
        # assumptions: [HplAssumption]
        # data_axioms: [HplProperty]
        # time_axioms: [HplProperty]
        default_strategies = {}
        pkg_imports = {"std_msgs"}
        types_by_msg = {}
        self.min_times = {p.pattern.trigger.topic: p.pattern.max_time
                     for p in time_axioms}
        # topic -> (type token, predicate)
        topics = self._mapping_hpl_assumptions(pubs, assumptions)
        self._mapping_hpl_axioms(topics, pubs, data_axioms)
        self.stage1 = Stage1Builder(topics, default_strategies,
            pkg_imports, types_by_msg)
        self.stage2 = Stage2Builder(topics, default_strategies,
            pkg_imports, types_by_msg)
        self.stage3 = Stage3Builder(topics, default_strategies,
            pkg_imports, types_by_msg)
        self.terminator = TerminatorBuilder(topics, default_strategies,
            pkg_imports, types_by_msg)
        self.deadline = deadline

    @property
    def default_strategies(self):
        assert (self.stage1.default_strategies is self.stage2.default_strategies
            and self.stage1.default_strategies is self.stage3.default_strategies)
        return self.stage1.default_strategies

    @property
    def pkg_imports(self):
        assert (self.stage1.pkg_imports is self.stage2.pkg_imports
            and self.stage1.pkg_imports is self.stage3.pkg_imports)
        return self.stage1.pkg_imports

    def build_strategies(self, prop):
        self.stage1.build(prop)
        self.stage2.build(prop)
        self.stage3.build(prop)
        self.terminator.build(prop)
        b_timeout = self.deadline
        a_min = 0
        a_max = 0
        if prop.pattern.is_response or prop.pattern.is_prevention:
            assert self.stage2.trigger is not None
            a_min = 1
            a_max = 2
            if prop.pattern.max_time < INF:
                b_timeout = prop.pattern.max_time
        elif prop.pattern.is_requirement:
            assert self.stage2.trigger is not None
            if prop.pattern.max_time < INF:
                a_max = 2
                b_timeout = prop.pattern.max_time
        else:
            assert self.stage2.trigger is None
            if prop.pattern.max_time < INF:
                b_timeout = prop.pattern.max_time
        min_time = 0.0
        if prop.scope.activator is None:
            assert self.stage1.activator is None
        else:
            # if prop.scope.activator.topic in publishers: assert
            assert self.stage1.activator is not None
        if prop.scope.terminator is None:
            assert self.terminator.terminator is None
        else:
            # if prop.scope.terminator.topic in publishers:
            #   assert self.terminator.terminator is not None
            if prop.scope.activator is not None:
                t1 = prop.scope.activator.topic
                t2 = prop.scope.terminator.topic
                if t1 == t2:
                    min_time = self.min_times.get(t1, 0.0)
        if not min_time < INF:
            raise StrategyError(("impossible to generate traces due to "
                "timing contraints: {}").format(prop))
        p = StrategyP(self.stage1.activator,
            list(self.stage1.strategies.values()))
        q = StrategyQ(self.terminator.terminator,
            list(self.stage3.strategies.values()), min_time)
        a = StrategyA(self.stage2.trigger,
            list(self.stage2.strategies.values()), a_min, a_max)
        b = StrategyB(list(self.stage3.strategies.values()), b_timeout)
        return Strategies(p, q, a, b)

    def _mapping_hpl_axioms(self, topics, publishers, axioms):
        for p in axioms:
            event = p.pattern.behaviour
            topic = event.topic
            assert p.pattern.is_absence
            if topic in publishers:
                phi = event.predicate.negate()
                rostype = publishers.get(topic)
                if rostype is not None:
                    prev = topics.get(topic)
                    if prev is not None:
                        assert prev[0] == rostype
                        phi = prev[1].join(phi)
                    topics[topic] = (rostype, phi)

    def _mapping_hpl_assumptions(self, publishers, assumptions):
        r = {}
        for event in assumptions:
            topic = event.topic
            rostype = publishers.get(topic)
            if rostype is not None:
                r[topic] = (rostype, event.predicate)
        for topic, rostype in publishers.items():
            if topic not in r:
                r[topic] = (rostype, HplVacuousTruth())
        return r


class StrategyBuilder(object):
    __slots__ = ("types_by_message", "counter", "default_strategies",
                 "pkg_imports")

    def __init__(self, default_strategies, pkg_imports, type_map):
        self.types_by_message = type_map
        self.counter = 0
        self.default_strategies = default_strategies
        self.pkg_imports = pkg_imports

    def _try_build(self, topic, rostype, phi, fun_name):
        try:
            self.strategies[topic] = self._build(
                    rostype, phi, topic=topic, fun_name=fun_name)
        except ContradictionError as e:
            pass # TODO log

    def _build(self, rostype, phi, topic=None, alias=None, fun_name="cms"):
        assert phi.is_predicate
        if phi.is_vacuous:
            if phi.is_true:
                return self._default_strategy(rostype, topic=topic)
            else:
                raise StrategyError(
                    "unsatisfiable predicate for '{}' ({}, '{}')".format(
                        topic, rostype, fun_name))
        self._add_default_strategy_for_type(rostype)
        # FIXME remove this and remake the strategy generator
        conditions = convert_to_old_format(phi.condition)
        strategy = self._msg_generator(rostype, conditions)
        self.pkg_imports.add(rostype.package)
        self.counter += 1
        name = "{}{}_{}_{}".format(
            fun_name, self.counter, rostype.package, rostype.message)
        return MsgStrategy(name, strategy.args, rostype.package,
            rostype.message, strategy.build(), False, topic, alias)

    def _default_strategy(self, rostype, topic=None):
        self._add_default_strategy_for_type(rostype)
        return MsgStrategy(rostype.type_name.replace("/", "_"),
            (), rostype.package, rostype.message, (), True, topic, None)

    def _add_default_strategy_for_type(self, rostype):
        assert rostype.is_message
        if rostype.type_name not in self.default_strategies:
            stack = [rostype]
            while stack:
                type_token = stack.pop()
                if type_token.is_primitive or type_token.is_header:
                    continue
                if type_token.is_time or type_token.is_duration:
                    continue
                if type_token.type_name in self.default_strategies:
                    continue
                if type_token.is_array:
                    stack.append(type_token.type_token)
                else:
                    assert type_token.is_message
                    self.pkg_imports.add(type_token.package)
                    self.default_strategies[type_token.type_name] = type_token
                    stack.extend(type_token.fields.values())

    def _msg_generator(self, type_token, conditions):
        strategy = MessageStrategyGenerator(type_token)
        for condition in conditions:
            # FIXME Selector should accept AST nodes instead of strings
            x = condition.operand1
            if x.is_function_call:
                assert x.function == "len", "what function is this"
                x = x.arguments[0]
            selector = Selector(str(x), type_token)
            strategy.ensure_generator(selector)
        for condition in conditions:
            self._set_condition(strategy, condition, type_token)
        return strategy

    def _set_condition(self, strategy, condition, type_token):
        operand1 = condition.operand1
        if operand1.is_function_call:
            assert operand1.function == "len", "what function is this"
            return self._set_attr_condition(strategy, condition, type_token)
        selector = Selector(str(operand1), type_token)
        try:
            value = self._value(condition.operand2, strategy, type_token)
        except KeyError as e:
            return
        if condition.operator == "=":
            strategy.set_eq(selector, value)
        elif condition.operator == "!=":
            strategy.set_neq(selector, value)
        elif condition.operator == "<":
            strategy.set_lt(selector, value)
        elif condition.operator == "<=":
            strategy.set_lte(selector, value)
        elif condition.operator == ">":
            strategy.set_gt(selector, value)
        elif condition.operator == ">=":
            strategy.set_gte(selector, value)
        elif condition.operator == "in":
            if condition.operand2.is_range:
                if condition.operand2.exclude_min:
                    strategy.set_gt(selector, value[0])
                else:
                    strategy.set_gte(selector, value[0])
                if condition.operand2.exclude_max:
                    strategy.set_lt(selector, value[1])
                else:
                    strategy.set_lte(selector, value[1])
            else:
                strategy.set_in(selector, value)

    def _set_attr_condition(self, strategy, condition, type_token):
        operand1 = condition.operand1
        assert operand1.is_function_call and operand1.function == "len"
        attr = operand1.function
        selector = Selector(str(operand1.arguments[0]), type_token)
        try:
            value = self._value(condition.operand2, strategy, type_token)
        except KeyError as e:
            return
        if condition.operator == "=":
            strategy.set_attr_eq(selector, value, attr=attr)
        elif condition.operator == "!=":
            strategy.set_attr_neq(selector, value, attr=attr)
        elif condition.operator == "<":
            strategy.set_attr_lt(selector, value, attr=attr)
        elif condition.operator == "<=":
            strategy.set_attr_lte(selector, value, attr=attr)
        elif condition.operator == ">":
            strategy.set_attr_gt(selector, value, attr=attr)
        elif condition.operator == ">=":
            strategy.set_attr_gte(selector, value, attr=attr)
        elif condition.operator == "in":
            if condition.operand2.is_range:
                if condition.operand2.exclude_min:
                    strategy.set_attr_gt(selector, value[0], attr=attr)
                else:
                    strategy.set_attr_gte(selector, value[0], attr=attr)
                if condition.operand2.exclude_max:
                    strategy.set_attr_lt(selector, value[1], attr=attr)
                else:
                    strategy.set_attr_lte(selector, value[1], attr=attr)
            else:
                assert False
                # strategy.set_in(selector, value)

    def _value(self, expr, strategy, type_token):
        if expr.is_accessor:
            msg = expr.base_message()
            if not msg.is_this_msg:
                assert msg.is_variable
                type_token = self.types_by_message[msg.name]
            # check for constants
            if expr.is_field and expr.message.is_value:
                ros_literal = type_token.constants.get(expr.field)
                if ros_literal is not None:
                    return ros_literal.value
            # It's hammer time!
            str_expr = str(expr)
            if str_expr.startswith("@"):
                str_expr = str_expr.split(".", 1)[-1]
            selector = Selector(str_expr, type_token)
            if msg.is_this_msg:
                return selector
            return strategy.make_msg_arg(msg.name, selector)
        n = False
        while not expr.is_value and expr.is_operator and expr.operator == "-":
            n = not n
            expr = expr.operand
        assert expr.is_value, repr(expr)
        if expr.is_literal:
            if n:
                return -expr.value
            else:
                return expr.value
        if expr.is_range:
            return (self._value(expr.min_value, strategy, type_token),
                    self._value(expr.max_value, strategy, type_token))
        if expr.is_set:
            return tuple(self._value(v, strategy, type_token)
                         for v in expr.values)
        raise StrategyError("unknown value type: " + repr(expr))

"""
>>> from z3 import *
>>> x, y = BitVecs('msg.field @i', 32)
>>> s = Optimize()
>>> s.add(x + y == 10)
>>> s.add(UGT(x, 0x7FFFFFFF))
>>> mx = s.minimize(x)
>>> s.check()
sat
>>> s.model()
[@i = 2147483658, msg.field = 2147483648]
>>> s.model()[x].as_signed_long()
-2147483648

>>> s = Optimize()
>>> s.add(x + y == 10)
>>> s.add(ULE(x, 0x7FFFFFFF))
>>> mx = s.maximize(x)
>>> s.check()
sat
>>> s.model()[x].as_signed_long()
2147483647
>>> s.model()
[@i = 2147483659, msg.field = 2147483647]

32-bit float: x = FP('x', FPSort(8, 24))
64-bit float: x = FP('x', FPSort(11, 53))
"""


"""
>>> from sympy import Symbol, solve
>>> x = Symbol('x')
>>> r = solve(x**2 - 1, x)
>>> r
[-1, 1]
>>> type(r[0])
<class 'sympy.core.numbers.NegativeOne'>
>>> r = solve(x - 4, x)
>>> r = solve(x > 3, x)
>>> r
(3 < x) & (x < oo)
>>> type(r)
And
>>> r.is_number
False
>>> r.is_Boolean
True
>>> bool(r)
True
>>> r.args
(3 < x, x < oo)
>>> from sympy import Not, Eq
>>> solve(Not(Eq(x, 4)), x)
(x > -oo) & (x < oo) & Ne(x, 4)
>>> r = solve(Not(Eq(x, 4)), x)
>>> r.args
(x > -oo, x < oo, Ne(x, 4))
>>> r.is_number
False
>>> r.is_Boolean
True
>>> from sympy import Or
>>> r = solve(Or(x > 4, x < -4), x)
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
  File "/home/andre/ros/harosenv/local/lib/python2.7/site-packages/sympy/solvers/solvers.py", line 1174, in solve
    solution = _solve(f[0], *symbols, **flags)
  File "/home/andre/ros/harosenv/local/lib/python2.7/site-packages/sympy/solvers/solvers.py", line 1511, in _solve
    f_num, sol = solve_linear(f, symbols=symbols)
  File "/home/andre/ros/harosenv/local/lib/python2.7/site-packages/sympy/solvers/solvers.py", line 2085, in solve_linear
    eq = lhs - rhs
TypeError: unsupported operand type(s) for -: 'Or' and 'int'
>>> Or(solve(x > 4, x), solve(x < -4, x))
((-oo < x) & (x < -4)) | ((4 < x) & (x < oo))
>>> _
((-oo < x) & (x < -4)) | ((4 < x) & (x < oo))
>>> _.args
((-oo < x) & (x < -4), (4 < x) & (x < oo))
>>> r = solve([x * 2 + 3 > 15, x >= -128, x < 128], x)
>>> r
(6 < x) & (x < 128)
"""


class Stage1Builder(StrategyBuilder):
    __slots__ = StrategyBuilder.__slots__ + (
        "topics", "strategies", "activator")

    def __init__(self, topics, default_strategies, pkg_imports, type_map):
        super(Stage1Builder, self).__init__(
            default_strategies, pkg_imports, type_map)
        self.topics = topics

    def build(self, prop):
        self.strategies = {}
        self.activator = None
        event = prop.scope.activator
        if event is None:
            return # activator is launch; this stage does not exist
        self._build_activator(event)
        self._build_randoms(event)

    def _build_activator(self, event):
        topic = event.topic
        if topic not in self.topics:
            # raise StrategyError("cannot publish on topic '{}'".format(topic))
            # no longer an error; passive activator
            self.activator = PASSIVE
            return
        rostype, assumed = self.topics.get(topic)
        phi = event.predicate.join(assumed)
        self.activator = self._build(
            rostype, phi, topic=topic, alias=event.alias, fun_name="s1cs")

    def _build_randoms(self, event):
        for topic, data in self.topics.items():
            rostype, assumed = data
            if topic == event.topic: # activator topic
                phi = event.predicate
                if phi.is_vacuous:
                    continue # no random messages
                else:
                    # cannot match activator
                    phi = phi.negate().join(assumed)
                    self._try_build(topic, rostype, phi, "s1cs")
            else: # random topic
                if assumed.is_vacuous and not assumed.is_true:
                    continue # no random messages
                self.strategies[topic] = self._build(
                    rostype, assumed, topic=topic, fun_name="s1cs")


class Stage2Builder(StrategyBuilder):
    __slots__ = StrategyBuilder.__slots__ + (
        "topics", "strategies", "trigger")

    def __init__(self, topics, default_strategies, pkg_imports, type_map):
        super(Stage2Builder, self).__init__(
            default_strategies, pkg_imports, type_map)
        self.topics = topics

    def build(self, prop):
        self.strategies = {}
        self.trigger = None
        trigger = prop.pattern.trigger
        terminator = prop.scope.terminator
        if prop.pattern.behaviour.topic in self.topics:
            raise StrategyError("topic '{}' is not advertised".format(
                prop.pattern.behaviour.topic))
        activator = prop.scope.activator
        if activator is not None and activator.alias is not None:
            rostype, assumed = self.topics.get(activator.topic)
            self.types_by_message[activator.alias] = rostype
        if (prop.pattern.is_requirement
                or prop.pattern.is_response or prop.pattern.is_prevention):
            assert trigger is not None
            self._build_trigger(trigger, terminator)
        #self._build_randoms(None, terminator)
        # it seems that we want to avoid random triggers after all
        self._build_randoms(trigger, terminator)

    def _build_trigger(self, trigger, terminator):
        topic = trigger.topic
        if topic not in self.topics:
            raise StrategyError("cannot publish on topic '{}'".format(topic))
        rostype, assumed = self.topics.get(topic)
        phi = trigger.predicate.join(assumed)
        if terminator is not None and terminator.topic == topic:
            if terminator.predicate.is_vacuous:
                raise StrategyError("trigger and terminator on the same topic")
            phi = phi.join(terminator.predicate.negate())
        self.trigger = self._build(
            rostype, phi, topic=topic, alias=trigger.alias, fun_name="s2cs")

    def _build_randoms(self, trigger, terminator):
        for topic, data in self.topics.items():
            rostype, assumed = data
            if trigger and topic == trigger.topic:
                phi = trigger.predicate
                if phi.is_vacuous:
                    continue # no random messages
                else: # cannot match trigger or terminator
                    phi = phi.negate()
                    if terminator and topic == terminator.topic:
                        psi = terminator.predicate
                        if psi.is_vacuous:
                            # TODO warning? trigger is impossible
                            continue # no random messages
                        else:
                            phi = phi.join(psi.negate())
                    phi = phi.join(assumed)
                    self._try_build(topic, rostype, phi, "s2cs")
            elif terminator and topic == terminator.topic:
                phi = terminator.predicate
                if phi.is_vacuous:
                    continue # no random messages
                else: # cannot match terminator
                    phi = phi.negate().join(assumed)
                    self._try_build(topic, rostype, phi, "s2cs")
            else: # random topic
                if assumed.is_vacuous and not assumed.is_true:
                    continue # no random messages
                self.strategies[topic] = self._build(
                    rostype, assumed, topic=topic, fun_name="s2cs")


class Stage3Builder(StrategyBuilder):
    __slots__ = StrategyBuilder.__slots__ + ("topics", "strategies")

    def __init__(self, topics, default_strategies, pkg_imports, type_map):
        super(Stage3Builder, self).__init__(
            default_strategies, pkg_imports, type_map)
        self.topics = topics

    def build(self, prop):
        self.strategies = {}
        #if not (prop.pattern.is_response or prop.pattern.is_prevention):
        #    return # other patterns do not have this stage
        self._build_randoms(prop.pattern.trigger, prop.scope.terminator)

    def _build_randoms(self, trigger, terminator):
        for topic, data in self.topics.items():
            rostype, assumed = data
            if trigger and topic == trigger.topic:
                phi = trigger.predicate
                if phi.is_vacuous:
                    continue # no random messages
                else: # cannot match trigger or terminator
                    phi = phi.negate()
                    if terminator and topic == terminator.topic:
                        psi = terminator.predicate
                        if psi.is_vacuous:
                            continue # no random messages
                        else:
                            phi = phi.join(psi.negate())
                    phi = phi.join(assumed)
                    self._try_build(topic, rostype, phi, "s3cs")
            elif terminator and topic == terminator.topic:
                phi = terminator.predicate
                if phi.is_vacuous:
                    continue # no random messages
                else: # cannot match terminator
                    phi = phi.negate().join(assumed)
                    self._try_build(topic, rostype, phi, "s3cs")
            else: # random topic
                if assumed.is_vacuous and not assumed.is_true:
                    continue # no random messages
                self.strategies[topic] = self._build(
                    rostype, assumed, topic=topic, fun_name="s3cs")


class TerminatorBuilder(StrategyBuilder):
    __slots__ = StrategyBuilder.__slots__ + ("topics", "terminator")

    def __init__(self, topics, default_strategies, pkg_imports, type_map):
        super(TerminatorBuilder, self).__init__(
            default_strategies, pkg_imports, type_map)
        self.topics = topics
        self.terminator = None

    def build(self, prop):
        self.terminator = None
        if prop.scope.terminator is not None:
            self._build_terminator(prop.scope.terminator)

    def _build_terminator(self, terminator):
        assert terminator is not None
        topic = terminator.topic
        if topic not in self.topics:
            return # previously an error
        rostype, assumed = self.topics[topic]
        phi = terminator.predicate
        if phi.is_vacuous:
            phi = assumed
        else:
            phi = phi.join(assumed)
        self.terminator = self._build(
            rostype, phi, topic=topic, fun_name="tcs")
