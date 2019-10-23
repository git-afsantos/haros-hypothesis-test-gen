# -*- coding: utf-8 -*-

#Copyright (c) 2019 André Santos
#
#Permission is hereby granted, free of charge, to any person obtaining a copy
#of this software and associated documentation files (the "Software"), to deal
#in the Software without restriction, including without limitation the rights
#to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
#copies of the Software, and to permit persons to whom the Software is
#furnished to do so, subject to the following conditions:

#The above copyright notice and this permission notice shall be included in
#all copies or substantial portions of the Software.

#THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
#OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
#THE SOFTWARE.


###############################################################################
# Imports
###############################################################################

from builtins import range # Python 2 and 3: forward-compatible
from collections import namedtuple
from itertools import chain as iterchain
import os

from haros.hpl.hpl_ast import HplAstObject
from haros.hpl.ros_types import get_type
from jinja2 import Environment, PackageLoader

from .events import MonitorTemplate
from .data import (
    MessageStrategyGenerator, CyclicDependencyError, InvalidFieldOperatorError,
)
from .selectors import Selector


###############################################################################
# Constants
###############################################################################

KEY = "haros_plugin_pbt_gen"

EMPTY_DICT = {}

INF = float("inf")


################################################################################
# Plugin Entry Point
################################################################################

config_num = 0

def configuration_analysis(iface, config):
    if not config.launch_commands or not config.nodes.enabled:
        return
    properties = [p for p in config.hpl_properties
                    if isinstance(p, HplAstObject)]
    if not properties:
        return
    assumptions = [p for p in config.hpl_assumptions
                     if isinstance(p, HplAstObject)]
    settings = config.user_attributes.get(KEY, EMPTY_DICT)
    _validate_settings(iface, settings)
    try:
        global config_num
        config_num += 1
        gen = TestGenerator(iface, config, properties, assumptions, settings)
        gen.make_tests(config_num)
    except SpecError as e:
        iface.log_error(e.message)


def _validate_settings(iface, settings):
    # TODO fill in the rest
    msg = "invalid setting for '{}': {}; expected one of {}; assuming {}"
    val = settings.get("extra_monitors")
    exp = (None, True, False, "safety")
    default = True
    if val not in exp:
        iface.log_warning(msg.format(val, exp, default))
        settings["extra_monitors"] = default


################################################################################
# Data Structures
################################################################################

PublisherTemplate = namedtuple("PublisherTemplate",
    ("topic", "type_token", "rospy_type", "strategies"))

TestTemplate = namedtuple("TestTemplate", ("monitor", "custom_strategies",
    "publishers", "subscribers", "pkg_imports", "property_text"))

Subscriber = namedtuple("Subscriber", ("topic", "type_token", "fake"))

CustomMsgStrategy = namedtuple("CustomMsgStrategy",
    ("name", "args", "pkg", "msg", "statements"))


class SpecError(Exception):
    pass


################################################################################
# Test Generator
################################################################################

class TestGenerator(object):
    def __init__(self, iface, config, properties, assumptions, settings):
        self.iface = iface
        self.config = config
        self.properties = properties
        self.assumptions = {p.topic: p.msg_filter for p in assumptions}
        self.settings = settings
        self.commands = config.launch_commands
        self.nodes = list(n.rosname.full for n in config.nodes.enabled)
        self.subbed_topics = self._get_open_subbed_topics()
        self.pubbed_topics = self._get_all_pubbed_topics()
        self._type_check_topics()
        self.subscribers = self._get_subscribers()
        self.pkg_imports = {"std_msgs"}
        for type_token in self.pubbed_topics.values():
            self.pkg_imports.add(type_token.package)
        self.default_strategies = self._get_default_strategies()

    def make_tests(self, config_num):
        monitors, tests = self._make_monitors_and_tests()
        for i in range(len(tests)):
            testable = tests[i]
            filename = "c{:03d}_test_{}.py".format(config_num, i+1)
            test_monitors = self._get_test_monitors(testable, monitors)
            self._write_test_files(tests[i], test_monitors, filename)
        if not tests:
            msg = "None of the given properties for {} is directly testable."
            msg = msg.format(self.config.name)
            self.iface.log_warning(msg)
            # TODO generate "empty" monitor, all others become secondary

    def _get_open_subbed_topics(self):
        ignored = self.settings.get("ignored", ())
        subbed = {} # topic -> msg_type (TypeToken)
        for topic in self.config.topics.enabled:
            if topic.subscribers and not topic.publishers:
                if topic.unresolved:
                    msg = "Skipping unresolved topic {} ({}).".format(
                        topic.rosname.full, self.config.name)
                    self.iface.log_warning(msg)
                elif topic.rosname.full in ignored:
                    msg = "Skipping ignored topic {} ({}).".format(
                        topic.rosname.full, self.config.name)
                    self.iface.log_warning(msg)
                else:
                    subbed[topic.rosname.full] = get_type(topic.type)
        return subbed

    def _get_all_pubbed_topics(self):
        ignored = self.settings.get("ignored", ())
        pubbed = {} # topic -> msg_type (TypeToken)
        for topic in self.config.topics.enabled:
            if topic.unresolved:
                msg = "Skipping unresolved topic {} ({}).".format(
                    topic.rosname.full, self.config.name)
                self.iface.log_warning(msg)
                continue
            if topic.publishers:
                if topic.rosname.full in ignored:
                    msg = "Skipping ignored topic {} ({}).".format(
                        topic.rosname.full, self.config.name)
                    self.iface.log_warning(msg)
                else:
                    pubbed[topic.rosname.full] = get_type(topic.type)
        return pubbed

    def _get_subscribers(self):
        subs = []
        for topic, type_token in self.subbed_topics.items():
            subs.append(Subscriber(topic, type_token, True))
        for topic, type_token in self.pubbed_topics.items():
            subs.append(Subscriber(topic, type_token, False))
        return subs

    def _get_default_strategies(self):
        queue = list(self.subbed_topics.values())
        strategies = {}
        while queue:
            new_queue = []
            for type_token in queue:
                if type_token.is_primitive or type_token.is_header:
                    continue
                if type_token.is_time or type_token.is_duration:
                    continue
                if type_token.is_array or type_token.type_name in strategies:
                    continue
                self.pkg_imports.add(type_token.package)
                strategies[type_token.type_name] = type_token
                new_queue.extend(type_token.fields.values())
            queue = new_queue
        return tuple(strategies.values())

    NO_TOPIC = "Configuration '{}' does not publish or subscribe topic '{}'"

    def _type_check_topics(self):
        for prop in self.properties:
            for event in prop.events():
                if event.is_publish:
                    base_type = self.pubbed_topics.get(event.topic)
                    if base_type is None:
                        try:
                            base_type = self.subbed_topics[event.topic]
                        except KeyError:
                            raise SpecError(self.NO_TOPIC.format(
                                self.config.name, event.topic))
                    self._type_check_msg_filter(event.msg_filter, base_type)
        for topic, msg_filter in self.assumptions.items():
            base_type = self.pubbed_topics.get(topic)
            if base_type is None:
                try:
                    base_type = self.subbed_topics[topic]
                except KeyError:
                    raise SpecError(self.NO_TOPIC.format(
                        self.config.name, topic))
            self._type_check_msg_filter(msg_filter, base_type)

    NO_FIELD = "Message type '{}' does not contain field '{}'"

    NAN = "Expected a number, but found {} ({})"

    NOT_LIST = "Expected a var-length array, but found {} ({})"

    def _type_check_msg_filter(self, msg_filter, base_type):
        for condition in msg_filter.conditions:
            try:
                selector = Selector(condition.field.token, base_type)
            except KeyError:
                raise SpecError(self.NO_FIELD.format(
                    base_type.type_name, condition.field.token))
            if condition.requires_number:
                if not selector.ros_type.is_number:
                    raise SpecError(self.NAN.format(
                        condition.field.token, base_type.type_name))
            # TODO check that values fit within types
        for condition in msg_filter.length_conditions:
            try:
                selector = Selector(condition.field.token, base_type)
            except KeyError:
                raise SpecError(self.NO_FIELD.format(
                    base_type.type_name, condition.field.token))
            if not (selector.ros_type.is_array
                    and not selector.ros_type.is_fixed_length):
                raise SpecError(self.NOT_LIST.format(
                    condition.field.token, base_type.type_name))

    def _make_monitors_and_tests(self):
        all_monitors = []
        tests = []
        for i in range(len(self.properties)):
            p = self.properties[i]
            uid = "P" + str(i + 1)
            monitor = MonitorTemplate(
                uid, p, self.pubbed_topics, self.subbed_topics)
            self._inject_assumptions(monitor)
            all_monitors.append(monitor)
            if monitor.is_testable:
                publishers = self._get_publishers(monitor.terminator)
                custom = CustomStrategyBuilder()
                custom.make_strategies(monitor, publishers, self.assumptions)
                # ^ custom.make_strategies() may change publishers
                custom.pkg_imports.update(self.pkg_imports)
                publishers = list(publishers.values())
                self._apply_slack(monitor)
                tests.append(TestTemplate(
                    monitor, custom.strategies, publishers, self.subscribers,
                    custom.pkg_imports, monitor.hpl_string))
            else:
                msg = ("Cannot produce a test script for the "
                       "following property: ")
                msg += monitor.hpl_string
                self.iface.log_warning(msg)
            monitor.variable_substitution()
        return all_monitors, tests

    def _get_test_monitors(self, test_case, monitors):
        extras = self.settings.get("extra_monitors", True)
        if extras is True:
            return monitors
        if extras is False:
            return (test_case.monitor,)
        if extras == "safety":
            ms = [m for m in monitors if m.is_safety]
            if test_case.monitor not in ms:
                ms.append(test_case.monitor)
            return ms
        # any other value is invalid; assume default behaviour
        return monitors

    def _get_publishers(self, terminator):
        avoid = set()
        if terminator is not None:
            for event in terminator.roots:
                avoid.add(event.topic)
        pubs = {}
        for topic, type_token in self.subbed_topics.items():
            if topic not in avoid:
                rospy_type = type_token.type_name.replace("/", ".")
                pubs[topic] = PublisherTemplate(
                    topic, type_token, rospy_type, [])
        return pubs

    def _inject_assumptions(self, monitor):
        event_map = {}
        for event in monitor.events:
            msg_filter = self.assumptions.get(event.topic)
            if msg_filter is not None:
                event.conditions.extend(msg_filter.conditions)
                event.length_conditions.extend(msg_filter.length_conditions)
            if event.alias:
                event_map[event.alias] = event
            lengths = {}
            for condition in event.conditions:
                self._length_for_field(condition.field.token,
                    event.type_token, lengths)
                self._length_for_value(condition.value, event.type_token,
                    lengths, event_map)
            # v -- NOTE saved_vars is probably not yet assigned
            for field_token in event.saved_vars.values():
                self._length_for_field(field_token, event.type_token, lengths)
            for token, min_length in lengths.items():
                event.add_min_length_condition(token, min_length)

    def _length_for_field(self, field_token, type_token, lengths):
        selector = Selector(field_token, type_token)
        array_expr = None
        for i in range(len(selector.accessors)):
            f = selector.accessors[i]
            if f.ros_type.is_array and not f.ros_type.is_fixed_length:
                field = selector.subselect(i+1)
                array_expr = field.expression
            elif array_expr is not None:
                min_len = lengths.get(array_expr, 0)
                if f.is_range:
                    pass # TODO
                elif not f.is_dynamic:
                    min_len = max(min_len, int(f.field_name) + 1)
                    if min_len > 0:
                        lengths[array_expr] = min_len
                array_expr = None

    def _length_for_value(self, hpl_value, type_token, lengths, event_map):
        if hpl_value.is_literal:
            return
        if hpl_value.is_reference:
            if hpl_value.message is not None:
                type_token = event_map[hpl_value.message].type_token
            if hpl_value.token in type_token.constants:
                return
            self._length_for_field(hpl_value.token, type_token, lengths)
        elif hpl_value.is_range:
            self._length_for_value(hpl_value.lower_bound, type_token,
                                   lengths, event_map)
            self._length_for_value(hpl_value.upper_bound, type_token,
                                   lengths, event_map)
        elif hpl_value.is_set:
            for v in hpl_value.values:
                self._length_for_value(v, type_token, lengths, event_map)
        elif not hpl_value.is_variable:
            raise TypeError("unknown value type: " + type(hpl_value).__name__)

    def _apply_slack(self, monitor):
        slack = self.settings.get("slack", 0.0)
        if slack < 0.0:
            raise ValueError("slack time cannot be negative")
        for event in monitor.events:
            event.duration += slack
            event.log_age += slack
            if event.external_timer is not None:
                event.external_timer += slack

    def _write_test_files(self, test_case, all_monitors, filename, debug=False):
        # test_case: includes monitor for which traces will be generated
        # all_monitors: used for secondary monitors
        env = Environment(
            loader=PackageLoader(KEY, "templates"),
            line_statement_prefix=None,
            line_comment_prefix=None,
            trim_blocks=True,
            lstrip_blocks=True,
            autoescape=False
        )
        if debug:
            template = env.get_template("debug_monitor.python.jinja")
        else:
            template = env.get_template("test_script.python.jinja")
        data = {
            "events": tuple(e for m in all_monitors for e in m.events),
            "main_monitor": test_case.monitor,
            "monitors": all_monitors,
            "default_strategies": self.default_strategies,
            "custom_strategies": test_case.custom_strategies,
            "publishers": test_case.publishers,
            "subscribers": test_case.subscribers,
            "settings": self.settings,
            "log_level": "DEBUG",
            "pkg_imports": test_case.pkg_imports,
            "property_text": test_case.property_text,
            "slack": self.settings.get("slack", 0.0),
            "nodes": self.nodes,
            "commands": self.commands
        }
        with open(filename, "w") as f:
            f.write(template.render(**data).encode("utf-8"))
        mode = os.stat(filename).st_mode
        mode |= (mode & 0o444) >> 2
        os.chmod(filename, mode)
        self.iface.export_file(filename)


################################################################################
# Custom Message Strategies
################################################################################

class CustomStrategyBuilder(object):
    def __init__(self):
        self.strategies = []
        self.pkg_imports = set()
        self.types_by_message = {}

    def fake_strategies(self, monitor):
        # this is basically just type checking
        # FIXME this is not working yet - cannot deal with aliases
        for event in monitor.events:
            try:
                strategy = self._msg_generator(
                    event.type_token, event.conditions)
                strategy.build()
            except (KeyError, IndexError) as e:
                raise SpecError("unable to find field:" + str(e))
            except CyclicDependencyError as e:
                raise SpecError("found cyclic dependencies: " + str(e))
            except InvalidFieldOperatorError as e:
                raise SpecError("invalid use of operator " + str(e))

    def make_strategies(self, monitor, publishers, assumptions):
        self.strategies = []
        for topic, pub in publishers.items():
            msg_filter = assumptions.get(topic)
            if msg_filter is not None:
                self.pkg_imports.add(pub.type_token.package)
                self.strategies.append(self._publisher(pub, msg_filter))
        if monitor.activator is not None:
            # the whole chain must happen
            for event in monitor.activator.events:
                assert event.topic in publishers, "{} not in {}; «{}»".format(
                    event.topic, tuple(publishers), monitor.hpl_string)
                pub = publishers[event.topic]
                self.pkg_imports.add(pub.type_token.package)
                if event.has_conditions:
                    self.strategies.append(self._event(event, pub))
                elif pub.strategies:
                    event.strategy = pub.strategies[-1]
        trigger = monitor.trigger
        if trigger is not None:
            if (monitor.is_safety
                    and not any(e.log_age < INF for e in trigger.leaves)):
                # make sure the roots do not happen; prevent the chain
                # TODO chain can theoretically be prevented at any point
                for event in trigger.roots:
                    if (event.topic in publishers and not event.has_conditions
                            and not event.ref_count):
                        # negation of any msg is no msg at all
                        del publishers[event.topic]
                for event in trigger.roots:
                    if event.topic in publishers and event.has_conditions:
                        pub = publishers[event.topic]
                        self.pkg_imports.add(pub.type_token.package)
                        strat = self._event(event, pub, negate=True)
                        self.strategies.append(strat)
                        pub.strategies.append(strat)
            elif monitor.is_liveness:
                # the whole chain must happen
                for event in trigger.events:
                    assert event.topic in publishers, "{} not in {}".format(
                        event.topic, publishers)
                    pub = publishers[event.topic]
                    self.pkg_imports.add(pub.type_token.package)
                    if event.has_conditions:
                        self.strategies.append(self._event(event, pub))
                    elif pub.strategies:
                        event.strategy = pub.strategies[-1]
        return self.strategies

    def _publisher(self, publisher, msg_filter):
        type_token = publisher.type_token
        self.types_by_message[None] = type_token
        strategy = self._strategy(type_token, msg_filter.conditions,
                                  msg_filter.length_conditions)
        publisher.strategies.append(strategy)
        return strategy

    def _event(self, event, publisher, negate=False):
        type_token = publisher.type_token
        self.types_by_message[event.alias] = type_token
        if event.alias is not None:
            self.types_by_message[None] = type_token
        if negate:
            # TODO improve this, not all must be negated at once;
            #   it should loop and negate one condition at a time.
            conditions = [c.negation() for c in event.conditions]
            len_conds = [c.negation() for c in event.length_conditions]
        else:
            conditions = event.conditions
            len_conds = event.length_conditions
        strategy = self._strategy(type_token, conditions, len_conds)
        event.strategy = strategy
        return strategy

    def _strategy(self, type_token, conditions, len_conditions):
        strategy = self._msg_generator(type_token, conditions, len_conditions)
        i = len(self.strategies) + 1
        name = "cms{}_{}_{}".format(i, type_token.package, type_token.message)
        return CustomMsgStrategy(name, strategy.args, type_token.package,
                                 type_token.message, strategy.build())

    def _msg_generator(self, type_token, conditions, len_conditions):
        strategy = MessageStrategyGenerator(type_token)
        for condition in iterchain(conditions, len_conditions):
            selector = Selector(condition.field.token, type_token)
            strategy.ensure_generator(selector)
        for condition in conditions:
            self._set_condition(strategy, condition, type_token)
        for condition in len_conditions:
            self._set_len_condition(strategy, condition, type_token)
        return strategy

    def _set_condition(self, strategy, condition, type_token):
        selector = Selector(condition.field.token, type_token)
        value = self._value(condition.value, strategy)
        if condition.is_eq:
            strategy.set_eq(selector, value)
        elif condition.is_neq:
            strategy.set_neq(selector, value)
        elif condition.is_lt:
            strategy.set_lt(selector, value)
        elif condition.is_lte:
            strategy.set_lte(selector, value)
        elif condition.is_gt:
            strategy.set_gt(selector, value)
        elif condition.is_gte:
            strategy.set_gte(selector, value)
        elif condition.is_in:
            if condition.value.is_range:
                if condition.value.exclude_lower:
                    strategy.set_gt(selector, value[0])
                else:
                    strategy.set_gte(selector, value[0])
                if condition.value.exclude_upper:
                    strategy.set_lt(selector, value[1])
                else:
                    strategy.set_lte(selector, value[1])
            else:
                strategy.set_in(selector, value)
        elif condition.is_not_in:
            if condition.value.is_range:
                strategy.set_not_in_range(selector, value[0], value[1],
                    exclude_min=condition.value.exclude_lower,
                    exclude_max=condition.value.exclude_upper)
            else:
                strategy.set_not_in(selector, value)

    def _set_len_condition(self, strategy, condition, type_token):
        selector = Selector(condition.field.token, type_token)
        value = self._value(condition.value, strategy)
        if condition.is_eq:
            strategy.set_attr_eq(selector, value, "length")
        elif condition.is_neq:
            strategy.set_attr_neq(selector, value, "length")
        elif condition.is_lt:
            strategy.set_attr_lt(selector, value, "length")
        elif condition.is_lte:
            strategy.set_attr_lte(selector, value, "length")
        elif condition.is_gt:
            strategy.set_attr_gt(selector, value, "length")
        elif condition.is_gte:
            strategy.set_attr_gte(selector, value, "length")
        elif condition.is_in:
            if condition.value.is_range:
                if condition.value.exclude_lower:
                    strategy.set_attr_gt(selector, value[0], "length")
                else:
                    strategy.set_attr_gte(selector, value[0], "length")
                if condition.value.exclude_upper:
                    strategy.set_attr_lt(selector, value[1], "length")
                else:
                    strategy.set_attr_lte(selector, value[1], "length")
            else:
                strategy.set_attr_in(selector, value, "length")
        elif condition.is_not_in:
            if condition.value.is_range:
                strategy.set_attr_not_in_range(selector, value[0], value[1],
                    "length", exclude_min=condition.value.exclude_lower,
                    exclude_max=condition.value.exclude_upper)
            else:
                strategy.set_attr_not_in(selector, value, "length")

    def _value(self, hpl_value, strategy):
        if hpl_value.is_reference:
            type_token = self.types_by_message[hpl_value.message]
            # check for constants
            if len(hpl_value.parts) == 1:
                ros_literal = type_token.constants.get(hpl_value.token)
                if ros_literal is not None:
                    return ros_literal.value
            selector = Selector(hpl_value.token, type_token)
            if hpl_value.message is None:
                return selector
            return strategy.make_msg_arg(hpl_value.message, selector)
        if hpl_value.is_literal:
            return hpl_value.value
        if hpl_value.is_range:
            return (self._value(hpl_value.lower_bound, strategy),
                    self._value(hpl_value.upper_bound, strategy))
        if hpl_value.is_set:
            return tuple(self._value(v, strategy) for v in hpl_value.values)
        raise TypeError("unknown value type: " + type(hpl_value).__name__)
