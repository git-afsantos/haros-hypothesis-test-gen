# -*- coding: utf-8 -*-

# SPDX-License-Identifier: MIT
# Copyright © 2019 André Santos

###############################################################################
# Imports
###############################################################################

from builtins import object, range, str
from collections import namedtuple
import io
from itertools import chain as iterchain
import os

from hpl.ast import HplVacuousTruth
from hplrv.rendering import TemplateRenderer
from rostypes.loader import get_type
from jinja2 import Environment, PackageLoader

from .events import MonitorTemplate
from .data import (
    MessageStrategyGenerator, CyclicDependencyError, InvalidFieldOperatorError,
    ContradictionError
)
from .schemas import schemas_for_property
from .selectors import Selector
from .util import StrategyError, convert_to_old_format
from .test_runner import TestRunner


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
    if (not config.launch_commands or not config.nodes.enabled
            or not config.hpl_properties):
        return
    settings = config.user_attributes.get(KEY, EMPTY_DICT)
    _validate_settings(iface, settings)
    try:
        global config_num
        config_num += 1
        gen = TestGenerator(iface, config, settings)
        gen.make_tests(config_num)
        if settings["run_tests"]:
            iface.log_debug("settings:run_tests is set to True")
            runner = TestRunner(iface, config)
            runner.start_roscore()
            try:
                runner.run_tests(gen.test_files)
            except Exception as test_err:
                iface.log_error("Error while running tests:\n" + str(test_err))
            finally:
                runner.shutdown_roscore()
    except SpecError as e:
        iface.log_error(e.message)


def _validate_settings(iface, settings):
    msg = "invalid setting for '{}': {}; expected one of {}; assuming {}"
    key = "extra_monitors"
    val = settings.get(key)
    exp = (None, True, False, "safety")
    default = True
    if val not in exp:
        iface.log_warning(msg.format(key, val, exp, default))
        settings[key] = default

    key = "deadline"
    val = settings.get(key)
    exp = (None, "float >= 0.0",)
    default = 10.0
    if val is None:
        settings[key] = default
    elif not isinstance(val, float) or val < 0.0:
        iface.log_warning(msg.format(key, val, exp, default))
        settings[key] = default

    key = "max_scopes"
    val = settings.get(key)
    exp = (None, "int >= 1",)
    default = 2
    if val is None:
        settings[key] = default
    elif not isinstance(val, int) or val < 1:
        iface.log_warning(msg.format(key, val, exp, default))
        settings[key] = default

    key = "run_tests"
    val = settings.get(key)
    exp = (None, True, False)
    default = False
    if val is None:
        settings[key] = default
    elif val not in exp:
        iface.log_warning(msg.format(key, val, exp, default))
        settings[key] = default


################################################################################
# Data Structures
################################################################################

PublisherTemplate = namedtuple("PublisherTemplate",
    ("topic", "type_token", "rospy_type"))

TestTemplate = namedtuple("TestTemplate",
    ("default_msg_strategies", "custom_msg_strategies",
     "trace_strategies", "monitor_templates",
     "test_case_template", "pkg_imports", "property_text"))

Subscriber = namedtuple("Subscriber", ("topic", "type_token", "fake"))

MsgStrategy = namedtuple("MsgStrategy",
    ("name", "args", "pkg", "msg", "statements", "is_default",
     "topic", "alias"))

PASSIVE = MsgStrategy("_", (), "std_msgs", "Header", (), True, "_", None)


class SpecError(Exception):
    pass


################################################################################
# Test Generator
################################################################################

class TestGenerator(object):
    def __init__(self, iface, config, settings):
        self.iface = iface
        self.config = config
        self.settings = settings
        self.commands = config.launch_commands
        self.subbed_topics = self._get_open_subbed_topics()
        self.pubbed_topics = self._get_all_pubbed_topics()
        assumptions = self._get_assumptions()
        data_axioms = self._get_data_axioms()
        time_axioms = self._get_time_axioms()
        self.strategies = StrategyManager(self.subbed_topics, assumptions,
            data_axioms, time_axioms, deadline=settings.get("deadline"))
        self.jinja_env = Environment(
            loader=PackageLoader(KEY, "templates"),
            line_statement_prefix=None,
            line_comment_prefix=None,
            trim_blocks=True,
            lstrip_blocks=True,
            autoescape=False
        )
        self.node_names = list(n.rosname.full for n in config.nodes.enabled)
        self.test_files = []

    def make_tests(self, config_num):
        self.test_files = []
        hpl_properties = self._filter_properties()
        monitors, axioms = self._make_monitors(hpl_properties)
        tests = self._make_test_templates(monitors, axioms)
        for i in range(len(tests)):
            testable = tests[i]
            filename = "c{:03d}_test_{}.py".format(config_num, i+1)
            self._write_test_files(tests[i], filename, axioms)
            self.test_files.append(filename)
        if not tests:
            msg = "None of the given properties for {} is directly testable."
            msg = msg.format(self.config.name)
            self.iface.log_warning(msg)
            # TODO generate "empty" monitor, all others become secondary

    def _filter_properties(self):
        properties = []
        for p in self.config.hpl_properties:
            if not p.is_fully_typed():
                self.iface.log_warning(
                    "Skipping untyped property:\n{}".format(p))
                continue
            if p.scope.activator is not None:
                topic = p.scope.activator.topic
                if topic not in self.subbed_topics:
                    if topic not in self.pubbed_topics:
                        continue
            if p.scope.terminator is not None:
                topic = p.scope.terminator.topic
                if topic not in self.subbed_topics:
                    if topic not in self.pubbed_topics:
                        continue
            if p.pattern.trigger is not None:
                topic = p.pattern.trigger.topic
                if topic not in self.subbed_topics:
                    if topic not in self.pubbed_topics:
                        continue
            topic = p.pattern.behaviour.topic
            if topic not in self.subbed_topics:
                if topic not in self.pubbed_topics:
                    continue
            properties.append(p)
        return properties

    # FIXME fetching type tokens should be part of HAROS
    def _get_open_subbed_topics(self):
        ignored = self.settings.get("ignored", ())
        subbed = {} # topic -> TypeToken
        for topic in self.config.topics.enabled:
            if topic.subscribers and not topic.publishers:
                if topic.unresolved or topic.type == "?":
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

    # FIXME fetching type tokens should be part of HAROS
    def _get_all_pubbed_topics(self):
        ignored = self.settings.get("ignored", ())
        pubbed = {} # topic -> msg_type (TypeToken)
        for topic in self.config.topics.enabled:
            if topic.unresolved or topic.type == "?":
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

    def _get_publishers(self):
        # FIXME build list based on self.strategies stages
        pubs = []
        for topic, type_token in self.subbed_topics.items():
            rospy_type = type_token.type_name.replace("/", ".")
            pubs.append(PublisherTemplate(topic, type_token, rospy_type))
        return pubs

    def _get_subscribers(self):
        subs = []
        for topic, type_token in self.subbed_topics.items():
            subs.append(Subscriber(topic, type_token, True))
        for topic, type_token in self.pubbed_topics.items():
            subs.append(Subscriber(topic, type_token, False))
        return subs

    def _make_monitors(self, hpl_properties):
        axioms = []
        monitors = []
        tr = TemplateRenderer()
        for i in range(len(hpl_properties)):
            p = hpl_properties[i]
            uid = "P" + str(i + 1)
            monitor = MonitorTemplate(
                uid, p, self.pubbed_topics, self.subbed_topics)
            monitor.variable_substitution()
            if monitor.is_input_only:
                axioms.append(monitor)
                data = {"monitor": monitor}
                monitor.python_eval = self._render_template(
                    "eval.python.jinja", data, strip=True)
            else:
                self._apply_slack(monitor)
                monitors.append(monitor)
            monitor.python = tr.render_monitor(p, class_name=monitor.class_name)
        return monitors, axioms

    def _make_test_templates(self, monitors, axioms):
        tests = []
        for i in range(len(monitors)):
            p = monitors[i].hpl_property
            try:
                strategies = self.strategies.build_strategies(p)
                data = {
                    "type_tokens": strategies['default_strategies'],
                    "random_headers": self.settings.get("random_headers", True),
                }
                py_default_msgs = self._render_template(
                    "default_msg_strategies.python.jinja",
                    data, strip=True)
                py_custom_msgs = self._render_template(
                    "custom_msg_strategies.python.jinja",
                    strategies, strip=True)
            except StrategyError as e:
                self.iface.log_warning(
                    "Cannot produce a test for:\n'{}'\n\n{}".format(p, e))
                continue
            ms = self._get_test_monitors(i, monitors)
            subs = self._get_subscribers()
            data = {
                "schemas": strategies["schemas"],
                "main_monitor": monitors[i].class_name,
                "monitors": ms,
                "axioms": axioms,
                "publishers": self._get_publishers(),
                "subscribers": subs,
                "commands": self.commands,
                "nodes": self.node_names,
                "settings": self.settings,
                "is_liveness": p.is_liveness,
            }
            py_test_case = self._render_template(
                "test_case.python.jinja", data, strip=True)
            py_monitors = [m.python for m in ms]
            pkg_imports = set(self.strategies.pkg_imports)
            for sub in subs:
                pkg_imports.add(sub.type_token.package)
            tests.append(TestTemplate(py_default_msgs, py_custom_msgs,
                self._render_trace_strategy(strategies), py_monitors,
                py_test_case, pkg_imports, monitors[i].hpl_string,))
        return tests

    def _get_test_monitors(self, i, monitors):
        extras = self.settings.get("extra_monitors", True)
        if extras is True:
            return monitors
        if extras is False:
            return (monitors[i],)
        if extras == "safety":
            ms = []
            for j in range(len(monitors)):
                if monitors[j].is_safety or j == i:
                    ms.append(monitors[j])
            return ms
        # any other value is invalid; assume default behaviour
        return monitors

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
        monitor.apply_slack(slack)

    def _write_test_files(self, test_template, filename, axioms, debug=False):
        data = {
            "pkg_imports": test_template.pkg_imports,
            "default_msg_strategies": test_template.default_msg_strategies,
            "custom_msg_strategies": test_template.custom_msg_strategies,
            "trace_strategies": test_template.trace_strategies,
            "monitors": test_template.monitor_templates,
            "axioms": [m.python for m in axioms],
            "eval_functions": [m.python_eval for m in axioms],
            "test_case": test_template.test_case_template,
            "log_level": "DEBUG",
            "property_text": test_template.property_text,
        }
        if debug:
            python = self._render_template(
                "debug_monitor.python.jinja", data, strip=False)
        else:
            python = self._render_template(
                "test_script.python.jinja", data, strip=False)
        with io.open(filename, "w", encoding="utf-8") as f:
            f.write(python.lstrip())
        mode = os.stat(filename).st_mode
        mode |= (mode & 0o444) >> 2
        os.chmod(filename, mode)
        self.iface.export_file(filename)

    def _render_trace_strategy(self, data):
        # data["reps"] = self.settings.get("max_scopes", 2)
        return self._render_template(
            "trace_strategies.python.jinja", data, strip=True)

    def _render_template(self, filename, data, strip=True):
        template = self.jinja_env.get_template(filename)
        text = template.render(**data)#.encode("utf-8")
        if strip:
            text = text.strip()
        return text

    def _get_assumptions(self):
        assumptions = []
        for p in self.config.hpl_assumptions:
            if p.is_fully_typed():
                assumptions.append(p)
            else:
                self.iface.log_warning(
                    "Skipping untyped assumption:\n{}".format(p))
        return assumptions

    def _get_data_axioms(self):
        axioms = []
        for p in self.config.hpl_properties:
            if not p.scope.is_global:
                continue # FIXME
            if not p.pattern.is_absence:
                continue
            b = p.pattern.behaviour
            if not b.topic in self.subbed_topics:
                continue
            if not p.is_fully_typed():
                self.iface.log_warning(
                    "Skipping untyped assumption:\n{}".format(p))
                continue
            if b.predicate.is_vacuous and b.predicate.is_true:
                del self.subbed_topics[b.topic]
            else:
                axioms.append(p)
        return axioms

    def _get_time_axioms(self):
        axioms = []
        for p in self.config.hpl_properties:
            if not p.scope.is_global:
                continue # FIXME
            if not p.pattern.is_prevention:
                continue
            a = p.pattern.trigger
            b = p.pattern.behaviour
            if not a.topic in self.subbed_topics:
                continue
            if not b.topic in self.subbed_topics:
                continue
            if a.topic != b.topic:
                continue
            if not a.predicate.is_vacuous or not a.predicate.is_true:
                continue
            if not b.predicate.is_vacuous or not b.predicate.is_true:
                continue
            if not p.is_fully_typed():
                self.iface.log_warning(
                    "Skipping untyped assumption:\n{}".format(p))
                continue
            axioms.append(p)
        return axioms


################################################################################
# Strategy Building
################################################################################

class StrategyManager(object):
    __slots__ = ('open_topics', 'pkg_imports', 'deadline')

    def __init__(self, topics, assumptions, data_axioms, time_axioms, deadline=10.0):
        # topics: topic -> ROS type token
        # assumptions: [HplAssumption]
        # data_axioms: [HplProperty]
        # time_axioms: [HplProperty]
        self.open_topics = {}
        self.pkg_imports = {'std_msgs'}
        for topic, ros_type in topics.items():
            self.open_topics[topic] = (ros_type, HplVacuousTruth())
            self.pkg_imports.add(ros_type.package)
        self._mapping_hpl_assumptions(assumptions)
        self._mapping_hpl_axioms(data_axioms)
        self.deadline = deadline

    def build_strategies(self, prop):
        alias_types = {}
        for high_level_event in prop.events():
            for event in high_level_event.simple_events():
                if event.alias is not None:
                    try:
                        ros_type, x = self.open_topics[event.topic]
                        alias_types[event.alias] = ros_type
                    except KeyError:
                        pass # not open subscribed topic
        builders = schemas_for_property(prop, unroll=1)
        # all_topics: {topic: (ros_type, assumption predicate)}
        # inf: int >= 0 (value to replace infinity with)
        #      int < 0 (treat infinity as unbounded/max. int)
        # deadline = int(self.deadline * 1000) # in milliseconds
        schemas = [b.build(self.open_topics, alias_types)
                   for b in reversed(builders)]
        # schemas: [SchemaInfo]
        # SchemaInfo: (name, [TraceSegment], string)
        default_strategies = set()
        custom_msg_strategies = []
        aliases = []
        for schema in schemas:
            for seg in schema.segments:
                for strategy in iterchain(seg.published, seg.spam.values()):
                    if strategy.is_default:
                        ros_type, x = self.open_topics[strategy.topic]
                        default_strategies.add(ros_type)
                    else:
                        custom_msg_strategies.append(strategy)
                    if strategy.alias is not None:
                        aliases.append(strategy.alias)
        return {
            'schemas': schemas,
            'default_strategies': default_strategies,
            'custom_msg_strategies': custom_msg_strategies,
            'aliases': aliases,
        }

    def _mapping_hpl_assumptions(self, assumptions):
        for event in assumptions:
            topic = event.topic
            info = self.open_topics.get(topic)
            if info is not None:
                phi = info[1].join(event.predicate)
                self.open_topics[topic] = (info[0], phi)

    def _mapping_hpl_axioms(self, axioms):
        for p in axioms:
            assert p.pattern.is_absence
            for event in p.pattern.behaviour.simple_events():
                topic = event.topic
                info = self.open_topics.get(topic)
                if info is not None:
                    phi = info[1].join(event.predicate.negate())
                    self.open_topics[topic] = (info[0], phi)
