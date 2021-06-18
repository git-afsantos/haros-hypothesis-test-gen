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

################################################################################
# Imports
################################################################################

from builtins import str
from builtins import object
from builtins import range # Python 2 and 3: forward-compatible
from collections import namedtuple

from hpl.ast import (
    HplSimpleEvent, HplValue #HplEventChain, HplChainDisjunction
)

from .util import convert_to_old_format, fake_set, fake_range, replace_base_msg


################################################################################
# Constants
################################################################################

INF = float("inf")


################################################################################
# Data Structures
################################################################################

HplFieldCondition = namedtuple("HplFieldCondition",
    ("field", "operator", "value"))


################################################################################
# Events
################################################################################

class EventTemplate(object):
    __slots__ = ("uid", "class_name", "var_name", "alias", "event_type",
                 "topic", "delay", "strategy", "duration", "ref_count",
                 "forks", "conditions", "saved_vars", "is_external", "is_root",
                 "seq_timer", "is_leaf", "external_timer", "is_under_timer",
                 "is_activator", "is_terminator", "is_trigger", "is_behaviour",
                 "dependencies", "dep_conditions", "log_level", "log_gap",
                 "log_age", "reads_state", "subsumes", "type_token")

    def __init__(self, uid, event):
        self.uid = uid # tuple(string | int)
        self._set_class_name()
        self.var_name = "e" + str(id(self)) # string
        self.alias = event.alias # string
        self.event_type = event.event_type # enum
        self.topic = event.topic # string
        self.type_token = None # TypeToken
        self.strategy = None # string
        self.delay = 0.0 # float
        self.duration = INF # float
        if event.predicate.is_vacuous:
            conditions = []
        else:
            conditions = convert_to_old_format(event.predicate.condition)
        self.conditions = [HplFieldCondition(c.operand1, c.operator, c.operand2)
                           for c in conditions]
        # ^ [HplFieldCondition]
        self.dep_conditions = {} # {tuple(event key): [HplFieldCondition]}
        self.ref_count = 0 # int    references to this event
        self.forks = [] # [EventTemplate]
        self.dependencies = [] # [EventTemplate]
        self.subsumes = [] # [EventTemplate]
        self.saved_vars = {} # {int (index): string (msg_field)}
        # message logging for properties over the past -----
        self.log_level = 0 # int
        self.log_gap = 0 # float
        self.log_age = INF # float
        # timers initiated by this event -------------------
        self.seq_timer = None # float
        self.external_timer = None # float
        # bool flags ---------------------------------------
        self.is_external = False
        self.is_root = False
        self.is_leaf = False
        self.is_activator = False
        self.is_terminator = False
        self.is_trigger = False
        self.is_behaviour = False
        self.reads_state = True
        self.is_under_timer = False

    @property
    def is_publish(self):
        return self.event_type == HplSimpleEvent.PUBLISH

    @property
    def is_receive(self):
        return self.event_type == HplSimpleEvent.PUBLISH and self.is_external

    @property
    def var_count(self):
        return len(self.saved_vars)

    @property
    def has_conditions(self):
        return bool(self.conditions)

    @property
    def msg_type(self):
        return self.type_token.type_name

    @property
    def has_duration(self):
        return self.duration >= 0.0 and self.duration < INF

    @property
    def has_log_age(self):
        return self.log_age >= 0.0 and self.log_age < INF

    def key(self):
        return self.uid[:-1]

    def get_slots(self):
        slots = [e.var_name for e in self.forks]
        slots.extend(e.var_name for e in self.dependencies)
        slots.extend(e.var_name for e in self.subsumes)
        if self.log_level > 0:
            slots.append("log")
        return slots

    def add_dep_condition(self, key, condition):
        if key in self.dep_conditions:
            self.dep_conditions[key].append(condition)
        else:
            self.dep_conditions[key] = [condition]

    def get_dep_conditions(self, key):
        return self.dep_conditions.get(key, [])

    def _set_class_name(self):
        parts = [str(i) for i in self.uid]
        parts.append("Listener")
        self.class_name = "_".join(parts)


class CompositeEventTemplate(object):
    __slots__ = ("uid", "events", "roots", "leaves")

    def __init__(self, uid, top_level_event):
        self.uid = uid
        self.events = []
        self.roots = []
        self.leaves = []
        #if isinstance(top_level_event, HplChainDisjunction):
        #    self._build_from_disjunction(top_level_event)
        #else:
        #    raise TypeError(top_level_event)

        # ---- glue code for new language version ----
        new_uid = uid + (1,)
        event = EventTemplate(new_uid, top_level_event)
        self.events.append(event)
        self.roots.append(event)
        event.is_root = True
        self.leaves.append(event)
        event.is_leaf = True

    def _build_from_disjunction(self, disjunction):
        assert len(disjunction.chains) >= 1
        chains = []
        for i in range(len(disjunction.chains)):
            uid = self.uid + (i + 1,)
            chain = self._build_from_chain(uid, disjunction.chains[i])
            chains.append(chain)
        if len(chains) > 1:
            for chain in chains:
                for other in chains:
                    if chain is other:
                        continue
                    chain[-1].subsumes.extend(other)

    def _build_from_chain(self, uid, chain):
        assert isinstance(chain, HplEventChain) and len(chain.events) >= 1
        new_events = []
        for i in range(len(chain.events)):
            new_uid = uid + (i + 1,)
            event = EventTemplate(new_uid, chain.events[i])
            self.events.append(event)
            new_events.append(event)
        for i in range(len(new_events) - 2, -1, -1):
            new_events[i].forks.append(new_events[i + 1])
        self.roots.append(new_events[0])
        new_events[0].is_root = True
        new_events[0].seq_timer = chain.duration
        self.leaves.append(new_events[-1])
        new_events[-1].is_leaf = True
        return new_events


################################################################################
# ROS Communications
################################################################################

class SubscriberTemplate(object):
    def __init__(self, topic, msg_type):
        self.topic = topic # string
        self.msg_type = msg_type # string
        self.events = [] # [EventTemplate]


################################################################################
# Monitors
################################################################################

class MonitorTemplate(object):
    __slots__ = ("index", "uid", "class_name", "is_liveness", "is_safety",
                 "events", "subs", "aliases", "activator", "terminator",
                 "trigger", "behaviour", "scope_timeout", "hpl_string",
                 "is_absence", "is_existence", "is_prevention", "is_response",
                 "is_precedence", "python", "python_eval", "is_input_only",
                 "hpl_property")

    _n = 0

    def __init__(self, uid, hpl_property, pubbed_topics, subbed_topics):
        # hpl_property :: HplProperty
        # pubbed_topics :: {string (topic): TypeToken}
        # subbed_topics :: {string (topic): TypeToken}
        MonitorTemplate._n += 1
        self.index = str(MonitorTemplate._n) # string
        self.uid = uid # string
        self.class_name = "Monitor" + self.index # string
        self.hpl_property = hpl_property
        self.hpl_string = str(hpl_property)
        self.is_liveness = hpl_property.is_liveness # bool
        self.is_safety = hpl_property.is_safety # bool
        self.is_absence = hpl_property.pattern.is_absence # bool
        self.is_existence = hpl_property.pattern.is_existence # bool
        self.is_precedence = hpl_property.pattern.is_requirement # bool
        self.is_response = hpl_property.pattern.is_response # bool
        self.is_prevention = hpl_property.pattern.is_prevention # bool
        self.events = [] # [EventTemplate]
        self.aliases = {} # {string (alias): EventTemplate}
        if hpl_property.pattern.is_absence or hpl_property.pattern.is_existence:
            self.scope_timeout = hpl_property.pattern.max_time
        else:
            self.scope_timeout = INF
        self._set_events(hpl_property)
        self._annotate_events(pubbed_topics, subbed_topics)
        self.subs = self._make_subs(hpl_property, pubbed_topics, subbed_topics)
        self.python = "raise NotImplementedError('monitor not implemented')"
        self.python_eval= ""
        self.is_input_only = all(e.topic in subbed_topics for e in self.events)

    @property
    def saved_vars(self):
        return sum(len(e.saved_vars) for e in self.events)

    @property
    def has_scope_timeout(self):
        return self.scope_timeout < INF

    def apply_slack(self, slack):
        assert slack >= 0.0
        if slack == 0.0:
            return
        if self.activator is not None:
            for event in self.activator.events:
                event.duration += slack
        if self.terminator is not None:
            for event in self.terminator.events:
                event.duration += slack
        if self.is_absence:
            for event in self.behaviour.events:
                event.delay += slack
        elif self.is_existence:
            for event in self.behaviour.events:
                event.duration += slack
        elif self.is_precedence:
            for event in self.trigger.events:
                event.duration += slack
                event.log_age += slack
            for event in self.behaviour.events:
                event.delay += slack
        elif self.is_response:
            for event in self.trigger.events:
                event.duration += slack
                if event.external_timer is not None:
                    event.external_timer += slack
            for event in self.behaviour.events:
                event.duration += slack
        elif self.is_prevention:
            for event in self.trigger.events:
                event.duration += slack
            for event in self.behaviour.events:
                event.delay += slack

    def _set_events(self, hpl_property):
        scope = hpl_property.scope
        pattern = hpl_property.pattern
        self.activator = None # CompositeEventTemplate
        if scope.activator is not None:
            self._set_activator(scope.activator)
        self.trigger = None # CompositeEventTemplate
        req = pattern.is_requirement
        if pattern.trigger is not None:
            self._set_trigger(pattern.trigger)
        self._set_behaviour(pattern.behaviour, req=req)
        if req:
            self._process_requirement(pattern.min_time, pattern.max_time)
        elif pattern.is_response or pattern.is_prevention:
            self._process_response(pattern.min_time, pattern.max_time)
        self.terminator = None # CompositeEventTemplate
        if scope.terminator is not None:
            self._set_terminator(scope.terminator)
        self._link_events()

    def _set_activator(self, top_level_event):
        self.activator = CompositeEventTemplate((self.uid, 1), top_level_event)
        var_name = "".join(("_p", self.index, "e"))
        for event in self.activator.events:
            self.events.append(event)
            event.is_activator = True
            event.var_name = var_name + str(len(self.events))
            if event.alias is not None:
                assert event.alias not in self.aliases
                self.aliases[event.alias] = event

    def _set_trigger(self, top_level_event):
        self.trigger = CompositeEventTemplate((self.uid, 2), top_level_event)
        var_name = "".join(("_p", self.index, "e"))
        for event in self.trigger.events:
            self.events.append(event)
            event.is_trigger = True
            event.var_name = var_name + str(len(self.events))
            if event.alias is not None:
                assert event.alias not in self.aliases
                self.aliases[event.alias] = event

    def _set_behaviour(self, top_level_event, req=False):
        self.behaviour = CompositeEventTemplate((self.uid, 3), top_level_event)
        var_name = "".join(("_p", self.index, "e"))
        for event in self.behaviour.events:
            self.events.append(event)
            event.is_behaviour = True
            event.var_name = var_name + str(len(self.events))
            if event.alias is not None:
                assert event.alias not in self.aliases
                self.aliases[event.alias] = event
            if req:
                event.dependencies.extend(self.trigger.leaves)

    def _set_terminator(self, top_level_event):
        self.terminator = CompositeEventTemplate((self.uid, 4), top_level_event)
        var_name = "".join(("_p", self.index, "e"))
        for event in self.terminator.events:
            self.events.append(event)
            event.is_terminator = True
            event.var_name = var_name + str(len(self.events))
            if event.alias is not None:
                assert event.alias not in self.aliases
                self.aliases[event.alias] = event

    def _process_requirement(self, gap, duration):
        for event in self.trigger.leaves:
            event.log_level = 1
            event.log_gap = gap
            event.log_age = duration
        for event in self.trigger.events:
            if event.alias is None:
                self._random_alias(event)
            for i in range(len(event.conditions) - 1, -1, -1):
                c = event.conditions[i]
                value = c.value
                field = c.field
                if value.is_accessor and value.base_message().is_variable:
                    # FIXME does not work for ranges and sets
                    alias = value.base_message().name
                    source = self.aliases[alias]
                    if source.is_behaviour:
                        del event.conditions[i]
                        field = replace_base_msg(field, repl=event.alias)
                        value = replace_base_msg(value)
                        if c.operator == "=":
                            source.conditions.append(HplFieldCondition(
                                value, "=", field))
                        elif c.operator == "!=":
                            source.conditions.append(HplFieldCondition(
                                value, "!=", field))
                        elif c.operator == "<":
                            source.conditions.append(HplFieldCondition(
                                value, ">", field))
                        elif c.operator == "<=":
                            source.conditions.append(HplFieldCondition(
                                value, ">=", field))
                        elif c.operator == ">":
                            source.conditions.append(HplFieldCondition(
                                value, "<", field))
                        elif c.operator == ">=":
                            source.conditions.append(HplFieldCondition(
                                value, "<=", field))
                        else:
                            assert False, "operator: " + c.operator

    def _process_response(self, delay, duration):
        if duration < INF:
            for event in self.trigger.leaves:
                event.external_timer = duration
            for event in self.behaviour.events:
                event.is_under_timer = True

    def _link_events(self):
        assert self.behaviour is not None
        if self.activator is not None:
            if self.is_absence or self.is_existence or self.is_precedence:
                for event in self.activator.leaves:
                    event.forks.extend(self.behaviour.roots)
            if self.is_precedence or self.is_response or self.is_prevention:
                assert self.trigger is not None
                for event in self.activator.leaves:
                    event.forks.extend(self.trigger.roots)
            if self.terminator is not None:
                for event in self.activator.leaves:
                    event.forks.extend(self.terminator.roots)
        if self.is_response or self.is_prevention:
            assert self.trigger is not None
            for event in self.trigger.leaves:
                event.forks.extend(self.behaviour.roots)

    def variable_substitution(self):
        var_count = 0
        s = self.is_safety
        for event in self.events:
            b = event.is_behaviour
            for i in range(len(event.conditions) - 1, -1, -1):
                c = event.conditions[i]
                if c.value.is_accessor:
                    var_count += self._var_substitution(event, i, c.field,
                        c.operator, c.value, var_count, s, b)
                elif c.value.is_set:
                    var_count += self._set_substitution(event, i, c.field,
                        c.operator, c.value, var_count, s, b)
                elif c.value.is_range:
                    var_count += self._range_substitution(event, i, c.field,
                        c.operator, c.value, var_count, s, b)

    def _var_substitution(self, event, i, field, op, value, var_count, s, b):
        inc = 0
        msg = value.base_message()
        if msg.is_variable:
            source = self.aliases[msg.name]
            source.ref_count += 1
            logged = s and b and source.is_trigger and not self.is_prevention
            token = str(value).split(".", 1)[-1]
            for j, field_ref in source.saved_vars.items():
                if field_ref == token:
                    var = _VariableSubstitution(j, ext=logged)
                    break
            else:
                var = _VariableSubstitution(var_count, ext=logged)
                source.saved_vars[var_count] = token
                inc += 1
            new_cond = HplFieldCondition(field, op, var)
            if logged:
                for leaf in self.trigger.leaves:
                    leaf.log_level = 2
                del event.conditions[i]
                event.add_dep_condition(source.key(), new_cond)
            else:
                event.conditions[i] = new_cond
        return inc

    def _set_substitution(self, event, i, field, op, hpl_set, var_count, s, b):
        inc = 0
        new_values = []
        logged = False
        replace = False
        for value in hpl_set.values:
            if not value.is_accessor:
                new_values.append(value)
                continue
            msg = value.base_message()
            if msg.is_variable:
                replace = True
                source = self.aliases[msg.name]
                source.ref_count += 1
                logged = logged or (s and b and source.is_trigger and not self.is_prevention)
                token = str(value).split(".", 1)[-1]
                for j, field_ref in source.saved_vars.items():
                    if field_ref == token:
                        var = _VariableSubstitution(j, ext=logged)
                        break
                else:
                    var = _VariableSubstitution(var_count, ext=logged)
                    source.saved_vars[var_count] = token
                    inc += 1
                new_values.append(var)
            else:
                new_values.append(value)
        if replace:
            new_cond = HplFieldCondition(field, op, fake_set(new_values))
            if logged:
                for leaf in self.trigger.leaves:
                    leaf.log_level = 2
                del event.conditions[i]
                event.add_dep_condition(source.key(), new_cond)
            else:
                event.conditions[i] = new_cond
        return inc

    def _range_substitution(self, event, i, field, op, hran, var_count, s, b):
        inc = 0
        new_values = []
        logged = False
        replace = False
        for value in (hran.min_value, hran.max_value):
            if not value.is_accessor:
                new_values.append(value)
                continue
            msg = value.base_message()
            if msg.is_variable:
                replace = True
                source = self.aliases[msg.name]
                source.ref_count += 1
                logged = logged or (s and b and source.is_trigger and not self.is_prevention)
                token = str(value).split(".", 1)[-1]
                for j, field_ref in source.saved_vars.items():
                    if field_ref == token:
                        var = _VariableSubstitution(j, ext=logged)
                        break
                else:
                    var = _VariableSubstitution(var_count, ext=logged)
                    source.saved_vars[var_count] = token
                    inc += 1
                new_values.append(var)
            else:
                new_values.append(value)
        if replace:
            new_range = fake_range(new_values[0], new_values[1],
                hran.exclude_min, hran.exclude_max)
            new_cond = HplFieldCondition(field, op, new_range)
            if logged:
                for leaf in self.trigger.leaves:
                    leaf.log_level = 2
                del event.conditions[i]
                event.add_dep_condition(source.key(), new_cond)
            else:
                event.conditions[i] = new_cond
        return inc

    def _annotate_events(self, pubbed_topics, subbed_topics):
        for event in self.events:
            if event.topic in pubbed_topics:
                event.type_token = pubbed_topics[event.topic]
            else:
                assert event.topic in subbed_topics, self.hpl_string
                event.is_external = True
                event.type_token = subbed_topics[event.topic]

    def _make_subs(self, prop, pubbed_topics, subbed_topics):
        subs = {}
        for event in self.events:
            sub = subs.get(event.topic)
            if sub is None:
                if event.is_publish and not event.is_external:
                    type_token = pubbed_topics[event.topic]
                else:
                    assert event.is_receive
                    type_token = subbed_topics[event.topic]
                rospy_type = type_token.type_name.replace("/", ".")
                sub = SubscriberTemplate(event.topic, rospy_type)
                subs[event.topic] = sub
            sub.events.append(event)
        return list(subs.values())

    def _random_alias(self, event):
        if event.alias is None:
            limit = 10000
            i = 0
            n = abs(hash(event.uid))
            a = "M" + str(n)
            while a in self.aliases and i < limit:
                i += 1
                n += 1
                if n < 0:
                    n = 0
                a = "M" + str(n)
            if i >= limit:
                raise RuntimeError("cannot generate random alias")
            event.alias = a
            self.aliases[a] = event


################################################################################
# Helper Classes
################################################################################

class _VariableSubstitution(HplValue):
    __slots__ = ("variable", "external")

    def __init__(self, var, ext=False):
        self.variable = var
        self.external = ext

    @property
    def is_variable(self):
        return True

    def __eq__(self, other):
        if not isinstance(other, _VariableSubstitution):
            return False
        return self.variable == other.variable

    def __hash__(self):
        return hash(self.variable)

    def __str__(self):
        return str(self.variable)

    def __repr__(self):
        return "{}({})".format(type(self).__name__, repr(self.variable))
