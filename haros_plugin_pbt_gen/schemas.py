# -*- coding: utf-8 -*-

# SPDX-License-Identifier: MIT
# Copyright © 2021 André Santos

###############################################################################
# Imports
###############################################################################

from __future__ import unicode_literals
from builtins import object, range, str
from collections import namedtuple

from hpl.ast import HplVacuousTruth

from .data import (
    MessageStrategyGenerator, CyclicDependencyError, InvalidFieldOperatorError,
    ContradictionError
)
from .selectors import Selector
from .util import StrategyError, convert_to_old_format


###############################################################################
# Constants
###############################################################################

INF = float('inf')
INT_INF = -1


################################################################################
# High-level Schema Builders
################################################################################

def schemas_for_property(prop, all_topics, inf=INT_INF, unroll=0):
    # all_topics: {topic: (ros_type, assumption predicate)}
    # inf: int >= 0 (value to replace infinity with)
    #      int < 0 (treat infinity as unbounded/max. int)
    # unroll: int >= 0 (how deep to unroll schemas)
    if unroll < 0:
        raise ValueError('unroll ({!r}) should be int >= 0'.format(unroll))
    schemas = _minimal_schemas(prop, all_topics, inf)
    return schemas


# Could be multiple because of disjunctions, etc..
# Looks like this:
#          forbid activator
#   +0..: publish activator
def _minimal_schemas(prop, all_topics, inf):
    builders = [TestSchemaBuilder(name='schema0')]
    _avoid_event(prop.scope.activator, builders)
    _ensure_event(prop.scope.activator, 0, INF, builders)
    if prop.pattern.is_absence:
        pass
    elif prop.pattern.is_existence:
        pass
    elif prop.pattern.is_requirement:
        pass
    elif prop.pattern.is_response or prop.pattern.is_prevention:
        _avoid_event(prop.pattern.trigger, builders)
        _avoid_event(prop.scope.terminator, builders)
        _ensure_event(prop.pattern.trigger, 0, INF, builders)
    else:
        assert False, str(prop.pattern)
    for i in range(len(builders)):
        builders[i] = builders[i].build(all_topics, inf=inf)
    return builders


def _avoid_event(event, builders):
    if event is None:
        return
    if event.is_simple_event:
        for builder in builders:
            builder.forbid(event.topic, event.predicate)
    elif event.is_event_disjunction:
        for builder in builders:
            for e in event.simple_events():
                builder.forbid(e.topic, e.predicate)
    else:
        assert False, str(type(event))

def _ensure_event(event, ts, tf, builders):
    if event is None:
        return
    if event.is_simple_event:
        for builder in builders:
            builder.new_timestamp(ts, tf)
            builder.publish(event.topic, event.predicate, alias=event.alias)
    elif event.is_event_disjunction:
        # disjunctions fork schemas
        events = list(event.simple_events())
        new_builders = []
        for builder in builders:
            builder.new_timestamp(ts, tf)
            for i in range(1, len(events)):
                e = events[i]
                name = 'schema' + str(len(builders) + len(new_builders))
                new_builders.append(builder.duplicate(name=name))
                new_builders[-1].publish(e.topic, e.predicate, alias=e.alias)
            e = events[0]
            builder.publish(e.topic, e.predicate, alias=e.alias)
        builders.extend(new_builders)
    else:
        assert False, str(type(event))


################################################################################
# Schema Building
################################################################################

class TestSchemaBuilder(object):
    __slots__ = ('name', 'segments',)

    def __init__(self, name='schema'):
        self.name = name
        self.segments = [TraceSegmentBuilder(0, 1)]

    def new_timestamp(self, lower_bound, upper_bound):
        if not (lower_bound >= 0 and lower_bound < INF):
            raise ValueError('interval lower_bound: ' + str(lower_bound))
        if not (upper_bound > lower_bound and upper_bound <= INF):
            raise ValueError('interval upper bound: ' + str(upper_bound))
        ts = int(lower_bound)
        tf = INT_INF if upper_bound == INF else int(upper_bound)
        self.segments.append(TraceSegmentBuilder(ts=ts, tf=tf))

    def publish(self, topic, predicate, alias=None):
        self.segments[-1].publish(topic, predicate, alias=alias)

    def forbid(self, topic, predicate):
        self.segments[-1].forbid(topic, predicate)

    def build(self, all_topics, inf=INT_INF):
        # all_topics: {topic: (ros_type, assumption)}
        schema = []
        for i in range(len(self.segments)):
            prefix = '{}_{}_'.format(self.name, i)
            schema.append(self.segments[i].build(all_topics,
                inf=inf, fun_name_prefix=prefix))
        return schema

    def duplicate(self, name='schema'):
        other = TestSchemaBuilder(name=name)
        other.segments = [segment.duplicate() for segment in self.segments]
        return other

    def __str__(self):
        return '#{}\n{}'.format(self.name,
            '\n'.join(str(s) for s in self.segments))


class TraceSegmentBuilder(object):
    __slots__ = (
        'lower_bound',      # int >= 0
        'upper_bound',      # int > lower_bound
        'publish_events',   # [MsgEvent]
        'forbid_events',    # [MsgEvent]
    )

    MsgEvent = namedtuple('MsgEvent', ('topic', 'predicate', 'alias'))

    TraceSegment = namedtuple('TraceSegment', (
        'lower_bound',  # int
        'upper_bound',  # int
        'published',    # [MsgStrategy]
        'spam',         # {topic: MsgStrategy}
        'is_single_instant', # bool
        'is_bounded'    # bool
    ))

    def __init__(self, ts=0, tf=INT_INF):
        assert ts >= 0, 'ts ({}) < 0'.format(ts)
        assert tf < 0 or tf > ts, 'tf ({}) <= ts ({})'.format(tf, ts)
        self.lower_bound = ts
        self.upper_bound = tf
        self.publish_events = [] # [MsgEvent]
        self.forbid_events = [] # [MsgEvent]

    @property
    def is_single_instant(self):
        ts = self.lower_bound
        tf = self.upper_bound
        return (tf > ts) and (tf - ts == 1)

    @property
    def is_bounded(self):
        return self.upper_bound > 0

    @property
    def has_publish_events(self):
        return len(self.publish_events) > 0

    @property
    def has_forbid_events(self):
        return len(self.forbid_events) > 0

    def publish(self, topic, predicate, alias=None):
        self.publish_events.append(self.MsgEvent(topic, predicate, alias))

    def forbid(self, topic, predicate):
        self.forbid_events.append(self.MsgEvent(topic, predicate, None))

    def event_strategies(self, all_topics, fun_name_prefix=''):
        # all_topics: {topic: (ros_type, assumption)}
        strategies = []
        for i in range(len(self.publish_events)):
            pe = self.publish_events[i]
            ros_type, assumed = all_topics[pe.topic]
            builder = MessageStrategyBuilder(pe.topic, ros_type)
            builder.assume(assumed)
            prefix = '{}pub{}'.format(fun_name_prefix, i)
            strategies.append(builder.build(predicate=pe.predicate,
                alias=pe.alias, fun_name_prefix=prefix))
        return strategies

    def spam_strategies(self, all_topics, fun_name_prefix=''):
        # all_topics: {topic: (ros_type, assumption)}
        strategies = {}
        for topic, info in all_topics.items():
            ros_type, assumed = info
            builder = MessageStrategyBuilder(topic, ros_type)
            builder.assume(assumed)
            for e in self.forbid_events:
                if e.topic == topic:
                    builder.assume(e.predicate.negate())
            prefix = fun_name_prefix + 'spam'
            strategies[topic] = builder.build(fun_name_prefix=prefix)
        return strategies

    def build(self, all_topics, inf=INT_INF, fun_name_prefix=''):
        return TraceSegment(
            self.lower_bound,
            self.upper_bound if self.is_bounded else inf,
            self.event_strategies(all_topics, fun_name_prefix=fun_name_prefix),
            self.spam_strategies(all_topics, fun_name_prefix=fun_name_prefix),
            self.is_single_instant,
            self.is_bounded
        )

    def duplicate(self):
        other = TraceSegmentBuilder(ts=self.lower_bound, tf=self.upper_bound)
        other.publish_events = list(self.publish_events)
        other.forbid_events = list(self.forbid_events)
        return other

    def __str__(self):
        if self.upper_bound < 0:
            time = '+{}..:'.format(self.lower_bound)
        else:
            time = '+{}..{}:'.format(self.lower_bound, self.upper_bound)
        ps = ''.join('\n  publish {} {{ {} }}'.format(e.topic, e.predicate)
                     for e in self.publish_events)
        fs = ''.join('\n  forbid {} {{ {} }}'.format(e.topic, e.predicate)
                     for e in self.forbid_events)
        return '{}{}{}'.format(time, ps, fs)


################################################################################
# Strategy Building
################################################################################

MsgStrategy = namedtuple('MsgStrategy',
    ('name', 'args', 'pkg', 'msg', 'statements', 'is_default',
     'topic', 'alias'))


# FIXME: building indexes of pkg_imports and default_strategies was removed
# from this class, in comparison with the original. It should be handled above.

class MessageStrategyBuilder(object):
    __slots__ = ('topic', 'ros_type', 'predicate')

    def __init__(self, topic, ros_type):
        self.topic = topic
        self.ros_type = ros_type
        self.predicate = HplVacuousTruth()

    @property
    def phi(self):
        return self.predicate

    @property
    def is_default(self):
        return self.predicate.is_vacuous and self.predicate.is_true

    @property
    def is_possible(self):
        return not self.predicate.is_vacuous or self.predicate.is_true

    def assume(self, predicate):
        self.predicate = self.predicate.join(assumption.predicate)

    def build(self, predicate=None, alias=None, fun_name_prefix='cms'):
        phi = self.predicate
        if predicate is not None:
            phi = predicate.join(phi)
        if phi.is_vacuous:
            if phi.is_true:
                return self.default_strategy()
            else:
                raise StrategyError.unsat(self.topic, self.ros_type)
        # FIXME remove this and remake the strategy generator
        conditions = convert_to_old_format(phi.condition)
        strategy = self._msg_generator(self.ros_type, conditions)
        name = '{}_{}_{}'.format(fun_name_prefix,
            self.ros_type.package, self.ros_type.message)
        return MsgStrategy(name, strategy.args, self.ros_type.package,
            self.ros_type.message, strategy.build(), False, self.topic, alias)

    def default_strategy(self):
        return MsgStrategy(self.ros_type.type_name.replace('/', '_'),
            (), self.ros_type.package, self.ros_type.message,
            (), True, self.topic, None)

    def _msg_generator(self, type_token, conditions):
        strategy = MessageStrategyGenerator(type_token)
        for condition in conditions:
            # FIXME Selector should accept AST nodes instead of strings
            x = condition.operand1
            if x.is_function_call:
                assert x.function == 'len', 'function: ' + x.function
                x = x.arguments[0]
            selector = Selector(str(x), type_token)
            strategy.ensure_generator(selector)
        for condition in conditions:
            self._set_condition(strategy, condition, type_token)
        return strategy

    def _set_condition(self, strategy, condition, type_token):
        operand1 = condition.operand1
        if operand1.is_function_call:
            assert operand1.function == 'len', 'function: ' + operand1.function
            return self._set_attr_condition(strategy, condition, type_token)
        selector = Selector(str(operand1), type_token)
        try:
            value = self._value(condition.operand2, strategy, type_token)
        except KeyError as e:
            return
        if condition.operator == '=':
            strategy.set_eq(selector, value)
        elif condition.operator == '!=':
            strategy.set_neq(selector, value)
        elif condition.operator == '<':
            strategy.set_lt(selector, value)
        elif condition.operator == '<=':
            strategy.set_lte(selector, value)
        elif condition.operator == '>':
            strategy.set_gt(selector, value)
        elif condition.operator == '>=':
            strategy.set_gte(selector, value)
        elif condition.operator == 'in':
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
        assert operand1.is_function_call and operand1.function == 'len'
        attr = operand1.function
        selector = Selector(str(operand1.arguments[0]), type_token)
        try:
            value = self._value(condition.operand2, strategy, type_token)
        except KeyError as e:
            return
        if condition.operator == '=':
            strategy.set_attr_eq(selector, value, attr=attr)
        elif condition.operator == '!=':
            strategy.set_attr_neq(selector, value, attr=attr)
        elif condition.operator == '<':
            strategy.set_attr_lt(selector, value, attr=attr)
        elif condition.operator == '<=':
            strategy.set_attr_lte(selector, value, attr=attr)
        elif condition.operator == '>':
            strategy.set_attr_gt(selector, value, attr=attr)
        elif condition.operator == '>=':
            strategy.set_attr_gte(selector, value, attr=attr)
        elif condition.operator == 'in':
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
            if str_expr.startswith('@'):
                str_expr = str_expr.split('.', 1)[-1]
            selector = Selector(str_expr, type_token)
            if msg.is_this_msg:
                return selector
            return strategy.make_msg_arg(msg.name, selector)
        n = False
        while not expr.is_value and expr.is_operator and expr.operator == '-':
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
        raise StrategyError('unknown value type: ' + repr(expr))
