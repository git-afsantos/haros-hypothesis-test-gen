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
from . import schema_parser
from .selectors import Selector
from .util import StrategyError, convert_to_old_format


###############################################################################
# Constants
###############################################################################

INF = float('inf')
INT_INF = -1


################################################################################
# Data Structures
################################################################################

SchemaInfo = namedtuple('SchemaInfo', (
    'name',     # string
    'segments', # [TraceSegment]
    'text',     # string
))

TraceSegment = namedtuple('TraceSegment', (
    'lower_bound',  # int
    'upper_bound',  # int
    'published',    # [MsgStrategy]
    'spam',         # {topic: MsgStrategy}
    'is_single_instant', # bool
    'is_bounded',   # bool
))

MsgStrategy = namedtuple('MsgStrategy', (
    'name',         # string
    'args',         # [string]
    'pkg',          # string
    'msg',          # string
    'statements',   # [hypothesis_ast.Statement]
    'is_default',   # bool
    'topic',        # string
    'alias',        # string
))


################################################################################
# Schema Refinement
################################################################################

def refine_schemas_with_time_axioms(builders, time_axioms):
    new_builders = []
    for builder in builders:
        refined = [builder]
        for axiom in time_axioms:
            _refine_with_time_axiom(refined, axiom)
        new_builders.extend(refined)
    return new_builders

def _refine_with_time_axiom(builders, axiom):
    try:
        if axiom.pattern.is_prevention:
            _sr_forbids(builders, axiom)
        else:
            pass # NYI
    except ContradictionError:
        raise StrategyError.unsat_axiom(axiom)

def _sr_forbids(builders, axiom):
    assert axiom.pattern.is_prevention
    a = axiom.pattern.trigger
    b = axiom.pattern.behaviour
    t = axiom.pattern.max_time
    assert a.is_simple_event
    assert b.is_simple_event
    if not a.predicate.is_vacuous:
        return # NYI
    if not a.predicate.is_true:
        return # nothing to do
    if b.predicate.is_vacuous and not b.predicate.is_true:
        return # nothing to do
    if a.topic == b.topic:
        _sr_forbids_eq_topic(builders, a, b, t)
    else:
        pass # NYI

def _sr_forbids_eq_topic(builders, a, b, t):
    assert a.topic == b.topic
    assert a.predicate.is_vacuous and a.predicate.is_true
    if t == INF:
        _sr_forbids_eq_topic_forever(builders, a, b)
    else:
        _sr_forbids_eq_topic_interval(builders, a, b, t)

def _sr_forbids_eq_topic_forever(builders, a, b):
    assert a.topic == b.topic
    assert a.predicate.is_vacuous and a.predicate.is_true
    assert not b.predicate.is_vacuous or b.predicate.is_true
    if b.predicate.is_vacuous and b.predicate.is_true:
        _sr_forbids_eq_topic_forever_all(builders, a, b)
    else:
        _sr_forbids_eq_topic_forever_some(builders, a, b)

def _sr_forbids_eq_topic_forever_all(builders, a, b):
    # allows 0 or 1 messages on topic
    new_builders = []
    for builder in builders:
        # start by counting mandatory triggers
        k = None
        for i in range(len(builder.segments)):
            n = builder.segments[i].publishes_topic(a.topic)
            if n > 1:
                raise ContradictionError()
            if n == 1:
                if k is not None:
                    raise ContradictionError()
                k = i
        if k is not None:
            # allow only that event
            builder.forbid_up_to(k, a.topic, a.predicate)
            builder.forbid_from(k, b.topic, b.predicate)
            continue # nothing else to do for this schema
        else:
            # explore every possible segment
            # add exactly 1 event per trace, at every point
            for i in range(len(builder.segments)):
                new = builder.duplicate()
                phi = new.segments[i].get_allowed_predicate(a.topic)
                if not phi.is_vacuous or phi.is_true:
                    new.segments[i].publish(a.topic, phi)
                    new.forbid_everywhere(a.topic, a.predicate)
                    new_builders.append(new)
            # change root schema - 0 events
            builder.forbid_everywhere(a.topic, a.predicate)
    builders.extend(new_builders)

def _sr_forbids_eq_topic_forever_some(builders, a, b):
    # the first message forbids some messages forever
    for builder in builders:
        # find the first mandatory trigger
        for k in range(len(builder.segments)):
            if builder.segments[k].publishes_topic(a.topic):
                break
        new_builders = []
        for i in range(k):
            # explore forks up until first mandatory trigger (if any)
            new = builder.duplicate()
            phi = new.segments[i].get_allowed_predicate(a.topic)
            if not phi.is_vacuous or phi.is_true:
                new.forbid_up_to(i, a.topic, a.predicate)
                # do not forbid on `i`, to allow more than one message
                # not needed to forbid trigger from this point onward
                new.segments[i].publish(a.topic, phi)
                new.forbid_from(i, b.topic, b.predicate)
                new_builders.append(new)
        restriction = b.predicate.negate()
        if k < len(builder.segments):
            # `k` only has to be refined for the forks
            # the original schema will only publish the first trigger on `k`
            for new in new_builders:
                new.segments[k].refine_published(b.topic, restriction)
            # change root schema - forbid from `k` onward
            builder.forbid_from(k, b.topic, b.predicate)
        for i in range(k + 1, len(builder.segments)):
            for new in new_builders:
                new.segments[i].refine_published(b.topic, restriction)
            builder.segments[i].refine_published(b.topic, restriction)
        builders.extend(new_builders)

def _sr_forbids_eq_topic_interval(builders, a, b, t):
    assert a.topic == b.topic
    assert a.predicate.is_vacuous and a.predicate.is_true
    assert not b.predicate.is_vacuous or b.predicate.is_true
    assert t > 0 and t < INF
    if b.predicate.is_vacuous and b.predicate.is_true:
        _sr_forbids_eq_topic_interval_all(builders, a, b, t)
    else:
        _sr_forbids_eq_topic_interval_some(builders, a, b, t)

def _sr_forbids_eq_topic_interval_all(builders, a, b, t):
    # there is no more than 1 message on topic per `t` time
    # NOTE: infinite schemas, in general; some cases left for eval
    assert a.topic == b.topic
    assert a.predicate.is_vacuous and a.predicate.is_true
    assert b.predicate.is_vacuous and b.predicate.is_true
    assert t > 0 and t < INF
    t = int(t * 1000) # milliseconds
    new_builders = []
    for builder in builders:
        if len(builder.segments) < 1:
            continue
        copy = builder.duplicate()
        changed = False
        # handle mandatory events first
        t_rem = 0
        for s in builder.segments:
            published = s.publishes_topic(a.topic)
            # no more than one message
            if published > 1:
                raise ContradictionError()
            # is this segment under restriction?
            if t_rem > 0:
                if published:
                    if s.is_bounded and s.upper_bound <= t_rem:
                        # restriction goes beyond this segment
                        # unable to push boundaries
                        raise ContradictionError()
                    s.lower_bound = t_rem # push lower bound
                else:
                    # forbid at lower bound for sure
                    # FIXME if upper bound is greater, it should split
                    # and alleviate the restriction
                    s.forbid(b.topic, b.predicate)
                    changed = True
                    # discount upper bound and trim examples with eval
                    if s.is_bounded:
                        t_rem -= s.upper_bound
                    else:
                        t_rem = 0
            if published:
                s.forbid(b.topic, b.predicate) # no random messages
                changed = True
                t_rem = t # apply restriction onward
        if changed:
            new_builders.append(copy)
        # handle optional events
        # in segments with mandatory triggers, random ones are not allowed
        # TODO
        #new_builders = []
        #was_allowed = False
        # the last segment does not matter
        #for i in range(len(builder.segments) - 1):
        #    s = builder.segments[i]
        #    s2 = builder.segments[i+1]
        #    allowed = s.is_topic_allowed(a.topic)
        #    if allowed:
        #        if s2.publishes_topic(b.topic):
        #            # split into case of zero and case of one
        #            new = builder.duplicate()
        #            changed = new.split_segment_at(i+1, t, l=False, r=True)
        #            if changed:
        #                s.forbid(a.topic, a.predicate)
        #                new.segments[i]
        #            # else: let eval figure it out
        #    was_allowed = allowed
    builders.extend(new_builders)


def _sr_forbids_eq_topic_interval_some(builders, a, b, t):
    # any message on topic forbids some messages for `t` time
    # NOTE: infinite schemas, in general; some cases left for eval
    assert a.topic == b.topic
    assert a.predicate.is_vacuous and a.predicate.is_true
    assert not b.predicate.is_vacuous
    assert t > 0 and t < INF
    # TODO


################################################################################
# Schema Parser Entry Point
################################################################################

def schema_from_text(text):
    statements = schema_parser.parse(text)
    builder = TestSchemaBuilder()
    for stmt in statements:
        if stmt[0] == 'publish':
            lower_bound, upper_bound = stmt[1]
            lower_bound /= 1000.0
            if upper_bound is None:
                upper_bound = INF
            else:
                upper_bound /= 1000.0
            builder.new_timestamp(lower_bound, upper_bound)
            ros_name, phi = stmt[2]
            builder.publish(ros_name, phi)
        elif stmt[0] == 'forbid':
            ros_name, phi = stmt[1]
            builder.forbid(ros_name, phi)
        else:
            assert False, 'schema statement: {}'.format(stmt[0])
    return builder

################################################################################
# High-level Schema Builders
################################################################################

def schemas_for_property(prop, unroll=0):
    # unroll: int >= 0 (how deep to unroll schemas)
    if unroll < 0 or unroll > 1:
        raise ValueError('expected 0 <= unroll ({!r}) <= 1'.format(unroll))
    if unroll == 1:
        return _unroll_1_schemas(prop)
    return _minimal_schemas(prop)


def _unroll_1_schemas(prop):
    if prop.pattern.is_absence:
        builders = _unroll_1_absence(prop)
    elif prop.pattern.is_existence:
        builders = _unroll_1_existence(prop)
    elif prop.pattern.is_requirement:
        builders = _unroll_1_requirement(prop)
    elif prop.pattern.is_response:
        builders = _unroll_1_response(prop)
    elif prop.pattern.is_prevention:
        builders = _unroll_1_prevention(prop)
    else:
        assert False, str(prop.pattern)
    # renaming
    for i in range(len(builders)):
        builders[i].name = 'u1_schema' + str(i)
    return builders


def _unroll_1_absence(prop):
    builders = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, builders)
    _ensure_event(prop.scope.activator, 0, INF, builders)
    _avoid_event(prop.scope.terminator, builders)
    return builders

def _unroll_1_existence(prop):
    t = prop.pattern.max_time # may be INF
    builders = []
    # terminator before timeout
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.scope.terminator, 0, t, new)
    builders.extend(new)
    if not prop.pattern.has_max_time:
        return builders
    # terminator after timeout
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.scope.terminator, t, INF, new)
    builders.extend(new)
    return builders

def _unroll_1_requirement(prop):
    t = prop.pattern.max_time # may be INF
    builders = []
    # zero triggers
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    builders.extend(new)
    # one trigger
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, INF, new)
    _avoid_event(prop.scope.terminator, new)
    builders.extend(new)
    # 2+ triggers, 2nd trigger before timeout
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, t, new)
    _avoid_event(prop.scope.terminator, new)
    builders.extend(new)
    if not prop.pattern.has_max_time:
        return builders
    # 2+ triggers, 2nd trigger after timeout
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, t, INF, new)
    _avoid_event(prop.scope.terminator, new)
    builders.extend(new)
    return builders

def _unroll_1_response(prop):
    t = prop.pattern.max_time # may be INF
    builders = []
    # one trigger, terminator before timeout
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.scope.terminator, 0, t, new)
    builders.extend(new)
    if prop.pattern.has_max_time and prop.scope.terminator is not None:
        # one trigger, terminator after timeout
        new = [TestSchemaBuilder()]
        _avoid_event(prop.scope.activator, new)
        _ensure_event(prop.scope.activator, 0, INF, new)
        _avoid_event(prop.pattern.trigger, new)
        _avoid_event(prop.scope.terminator, new)
        _ensure_event(prop.pattern.trigger, 0, INF, new)
        _avoid_event(prop.pattern.trigger, new)
        _avoid_event(prop.scope.terminator, new)
        _ensure_event(prop.scope.terminator, t, INF, new)
        builders.extend(new)
    # 2nd trigger before timeout, terminator before timeout
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, t, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.scope.terminator, 0, t, new)
    builders.extend(new)
    if not prop.pattern.has_max_time:
        return builders
    # 2nd trigger after timeout, terminator before timeout
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, t, INF, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.scope.terminator, 0, t, new)
    builders.extend(new)
    if prop.scope.terminator is not None:
        # 2nd trigger before timeout, terminator after timeout
        new = [TestSchemaBuilder()]
        _avoid_event(prop.scope.activator, new)
        _ensure_event(prop.scope.activator, 0, INF, new)
        _avoid_event(prop.pattern.trigger, new)
        _avoid_event(prop.scope.terminator, new)
        _ensure_event(prop.pattern.trigger, 0, INF, new)
        _avoid_event(prop.pattern.trigger, new)
        _avoid_event(prop.scope.terminator, new)
        _ensure_event(prop.pattern.trigger, 0, t, new)
        _avoid_event(prop.scope.terminator, new)
        _ensure_event(prop.scope.terminator, t, INF, new)
        builders.extend(new)
        # 2nd trigger after timeout, terminator after timeout
        new = [TestSchemaBuilder()]
        _avoid_event(prop.scope.activator, new)
        _ensure_event(prop.scope.activator, 0, INF, new)
        _avoid_event(prop.pattern.trigger, new)
        _avoid_event(prop.scope.terminator, new)
        _ensure_event(prop.pattern.trigger, 0, INF, new)
        _avoid_event(prop.pattern.trigger, new)
        _avoid_event(prop.scope.terminator, new)
        _ensure_event(prop.pattern.trigger, t, INF, new)
        _avoid_event(prop.scope.terminator, new)
        _ensure_event(prop.scope.terminator, t, INF, new)
        builders.extend(new)
    return builders

def _unroll_1_prevention(prop):
    t = prop.pattern.max_time # may be INF
    builders = []
    # one trigger
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    builders.extend(new)
    # 2+ triggers, 2nd trigger before timeout
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, t, new)
    _avoid_event(prop.scope.terminator, new)
    builders.extend(new)
    if not prop.pattern.has_max_time:
        return builders
    # 2+ triggers, 2nd trigger after timeout
    new = [TestSchemaBuilder()]
    _avoid_event(prop.scope.activator, new)
    _ensure_event(prop.scope.activator, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, 0, INF, new)
    _avoid_event(prop.pattern.trigger, new)
    _avoid_event(prop.scope.terminator, new)
    _ensure_event(prop.pattern.trigger, t, INF, new)
    _avoid_event(prop.scope.terminator, new)
    builders.extend(new)
    return builders


def _unroll_2_schemas(prop, schemas):
    pass


# Could be multiple because of disjunctions, etc..
# Looks like this:
#          forbid activator
#   +0..: publish activator
#          forbid trigger
#          forbid terminator
#   +0..: publish trigger
def _minimal_schemas(prop):
    builders = [TestSchemaBuilder(name='u0_schema0')]
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
        _ensure_event(prop.pattern.trigger, 0, INF, builders, 'u0_schema')
    else:
        assert False, str(prop.pattern)
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

def _ensure_event(event, ts, tf, builders, schema_name='schema'):
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
                name = schema_name + str(len(builders) + len(new_builders))
                new_builders.append(builder.duplicate(name=name))
                new_builders[-1].publish(e.topic, e.predicate, alias=e.alias)
            e = events[0]
            builder.publish(e.topic, e.predicate, alias=e.alias)
        builders.extend(new_builders)
    else:
        assert False, str(type(event))

def _ensure_event_before_after(event, ts, tf, builders, schema_name='schema'):
    if event is None:
        return
    new_builders = [b.duplicate() for b in builders]
    _ensure_event(event, ts, tf, builders, schema_name)
    for i in range(len(new_builders)):
        new_builders[i].name = schema_name + str(len(builders) + i)
    _ensure_event(event, tf, INF, new_builders, schema_name)


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
        ts = int(lower_bound * 1000)
        tf = INT_INF if upper_bound == INF else int(upper_bound * 1000)
        self.segments.append(TraceSegmentBuilder(ts=ts, tf=tf))

    def publish(self, topic, predicate, alias=None):
        self.segments[-1].publish(topic, predicate, alias=alias)

    def forbid(self, topic, predicate):
        self.segments[-1].forbid(topic, predicate)

    def forbid_everywhere(self, topic, predicate):
        for segment in self.segments:
            segment.forbid(topic, predicate)

    def forbid_up_to(self, i, topic, predicate):
        for j in range(0, i):
            self.segments[j].forbid(topic, predicate)

    def forbid_from(self, i, topic, predicate):
        for j in range(i, len(self.segments)):
            self.segments[j].forbid(topic, predicate)

    def split_segment_at(self, i, t, l=True, r=True):
        # l: keep publish_events to the left
        # r: keep publish_events to the right
        # l and r: duplicate publish_events
        # not l and not r: drop all publish_events
        segment = self.segments[i]
        if segment.is_bounded and segment.upper_bound <= t:
            return False
        if segment.lower_bound >= t:
            return False
        assert segment.lower_bound < t
        assert not segment.is_bounded or segment.upper_bound > t
        new = segment.duplicate()
        new.lower_bound = 0
        segment.upper_bound = t
        if new.is_bounded:
            new.upper_bound -= t
        if not l:
            segment.publish_events = []
        if not r:
            new.publish_events = []
        self.segments.insert(i + 1, new)
        return True

    def build(self, all_topics, alias_types, inf=INT_INF):
        # all_topics: {topic: (ros_type, assumption)}
        # alias_types: {alias: ros_type}
        schema = []
        for i in range(len(self.segments)):
            segment_name = '{}_{}'.format(self.name, i)
            schema.append(self.segments[i].build(all_topics, alias_types,
                inf=inf, name=segment_name))
        return SchemaInfo(self.name, schema, str(self))

    def duplicate(self, name='schema'):
        other = TestSchemaBuilder(name=name)
        other.segments = [segment.duplicate() for segment in self.segments]
        return other

    def __str__(self):
        segments = []
        if len(self.segments) > 0:
            segments.append(self.segments[0].lean_str())
        for s in self.segments[1:]:
            segments.append(str(s))
        return '#{}\n{}'.format(self.name, '\n'.join(s for s in segments))


class TraceSegmentBuilder(object):
    __slots__ = (
        'lower_bound',      # int >= 0
        'upper_bound',      # int > lower_bound
        'publish_events',   # [MsgEvent]
        'forbid_events',    # [MsgEvent]
    )

    MsgEvent = namedtuple('MsgEvent', ('topic', 'predicate', 'alias'))

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

    def publishes_topic(self, topic):
        n = 0
        for event in self.publish_events:
            if event.topic == topic:
                n += 1
        return n

    def forbids_topic(self, topic):
        n = 0
        for event in self.forbid_events:
            if event.topic == topic:
                n += 1
        return n

    def publish(self, topic, predicate, alias=None):
        self.publish_events.append(self.MsgEvent(topic, predicate, alias))

    def forbid(self, topic, predicate):
        if predicate.is_vacuous:
            if not predicate.is_true:
                return
            assert predicate.is_true
            # subsumes all other occurrences
            for i in range(len(self.forbid_events) - 1, -1, -1):
                if self.forbid_events[i].topic == topic:
                    del self.forbid_events[i]
        else:
            for event in self.forbid_events:
                if event.topic != topic:
                    continue
                if not event.predicate.is_vacuous:
                    continue
                if event.predicate.is_true:
                    return # subsumed
        self.forbid_events.append(self.MsgEvent(topic, predicate, None))

    def get_allowed_predicate(self, topic):
        phi = HplVacuousTruth() # any message allowed
        for event in self.forbid_events:
            if event.topic == topic:
                phi = phi.join(event.predicate.negate())
        return phi

    def is_topic_allowed(self, topic):
        phi = self.get_allowed_predicate(topic)
        return not phi.is_vacuous or phi.is_true

    def refine_published(self, topic, predicate):
        n = 0
        for i in range(len(self.publish_events)):
            event = self.publish_events[i]
            if event.topic == topic:
                phi = event.predicate.join(predicate)
                self.publish_events[i] = event._replace(predicate=phi)
                n += 1
        return n # how many events were changed

    def event_strategies(self, all_topics, alias_types, name='segment'):
        # all_topics: {topic: (ros_type, assumption)}
        strategies = []
        for i in range(len(self.publish_events)):
            pe = self.publish_events[i]
            try:
                ros_type, assumed = all_topics[pe.topic]
            except KeyError:
                raise StrategyError.not_open_sub(pe.topic)
            version = '{}_{}p'.format(name, i)
            builder = MessageStrategyBuilder(pe.topic, ros_type, ver=version)
            builder.assume(assumed)
            strategies.append(builder.build(alias_types,
                predicate=pe.predicate, alias=pe.alias))
        return strategies

    def spam_strategies(self, all_topics, alias_types, name='segment'):
        # all_topics: {topic: (ros_type, assumption)}
        strategies = {}
        i = 0
        for topic, info in all_topics.items():
            ros_type, assumed = info
            version = '{}_{}s'.format(name, i)
            i += 1
            builder = MessageStrategyBuilder(topic, ros_type, ver=version)
            builder.assume(assumed)
            for e in self.forbid_events:
                if e.topic == topic:
                    builder.assume(e.predicate.negate())
            try:
                strategies[topic] = builder.build(alias_types)
            except ContradictionError:
                pass
        return strategies

    def build(self, all_topics, alias_types, inf=INT_INF, name='segment'):
        try:
            return TraceSegment(
                self.lower_bound,
                self.upper_bound if self.is_bounded else inf,
                self.event_strategies(all_topics, alias_types, name=name),
                self.spam_strategies(all_topics, alias_types, name=name),
                self.is_single_instant,
                self.is_bounded
            )
        except ContradictionError as e:
            raise StrategyError(e)

    def duplicate(self):
        other = TraceSegmentBuilder(ts=self.lower_bound, tf=self.upper_bound)
        other.publish_events = list(self.publish_events)
        other.forbid_events = list(self.forbid_events)
        return other

    def lean_str(self):
        if self.lower_bound != 0:
            return str(self)
        if not self.is_single_instant:
            return str(self)
        if len(self.publish_events) > 0:
            return str(self)
        return '\n  '.join('forbid {} {}'.format(e.topic, e.predicate)
                           for e in self.forbid_events)

    def __str__(self):
        if not self.is_bounded:
            time = '+{}..:'.format(self.lower_bound)
        else:
            time = '+{}..{}:'.format(self.lower_bound, self.upper_bound)
        ps = ''.join('\n  publish {} {}'.format(e.topic, e.predicate)
                     for e in self.publish_events)
        fs = ''.join('\n  forbid {} {}'.format(e.topic, e.predicate)
                     for e in self.forbid_events)
        return '{}{}{}'.format(time, ps, fs)


################################################################################
# Strategy Building
################################################################################

class MessageStrategyBuilder(object):
    __slots__ = ('topic', 'ros_type', 'predicate', 'version')

    def __init__(self, topic, ros_type, ver='1'):
        self.topic = topic
        self.ros_type = ros_type
        self.predicate = HplVacuousTruth()
        self.version = ver

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
        self.predicate = self.predicate.join(predicate)

    def build(self, alias_types, predicate=None, alias=None):
        phi = self.predicate
        if predicate is not None:
            phi = predicate.join(phi)
        if phi.is_vacuous:
            if phi.is_true:
                return self.default_strategy()
            else:
                # raise StrategyError.unsat(self.topic, self.ros_type)
                raise ContradictionError('{} ({})'.format(
                    self.topic, self.ros_type))
        # FIXME remove this and remake the strategy generator
        conditions = convert_to_old_format(phi.condition)
        strategy = self._msg_generator(self.ros_type, conditions, alias_types)
        name = '{}_{}_{}'.format(self.ros_type.package,
            self.ros_type.message, self.version)
        return MsgStrategy(name, strategy.args, self.ros_type.package,
            self.ros_type.message, strategy.build(), False, self.topic, alias)

    def default_strategy(self):
        return MsgStrategy(self.ros_type.type_name.replace('/', '_'),
            (), self.ros_type.package, self.ros_type.message,
            (), True, self.topic, None)

    def _msg_generator(self, type_token, conditions, alias_types):
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
            self._set_condition(strategy, condition, type_token, alias_types)
        return strategy

    def _set_condition(self, strategy, condition, type_token, alias_types):
        operand1 = condition.operand1
        if operand1.is_function_call:
            assert operand1.function == 'len', 'function: ' + operand1.function
            return self._set_attr_condition(strategy, condition, type_token, alias_types)
        selector = Selector(str(operand1), type_token)
        try:
            value = self._value(condition.operand2, strategy, type_token, alias_types)
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

    def _set_attr_condition(self, strategy, condition, type_token, alias_types):
        operand1 = condition.operand1
        assert operand1.is_function_call and operand1.function == 'len'
        attr = operand1.function
        selector = Selector(str(operand1.arguments[0]), type_token)
        try:
            value = self._value(condition.operand2, strategy, type_token, alias_types)
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

    def _value(self, expr, strategy, type_token, alias_types):
        if expr.is_accessor:
            msg = expr.base_message()
            if not msg.is_this_msg:
                assert msg.is_variable
                type_token = alias_types[msg.name]
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
            return (self._value(expr.min_value, strategy, type_token, alias_types),
                    self._value(expr.max_value, strategy, type_token, alias_types))
        if expr.is_set:
            return tuple(self._value(v, strategy, type_token, alias_types)
                         for v in expr.values)
        raise StrategyError('unknown value type: ' + repr(expr))
