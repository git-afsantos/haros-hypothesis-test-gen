# -*- coding: utf-8 -*-

# SPDX-License-Identifier: MIT
# Copyright © 2021 André Santos

###############################################################################
# Imports
###############################################################################

from __future__ import unicode_literals
from builtins import object
from collections import namedtuple

from hpl.ast import HplVacuousTruth

# from .events import MonitorTemplate
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


################################################################################
# Schema Building
################################################################################

StrategyP = namedtuple('P', ('strategy', 'spam'))
StrategyQ = namedtuple('Q', ('strategy', 'spam', 'min_time'))
StrategyA = namedtuple('A', ('strategy', 'spam', 'min_num', 'max_num'))
StrategyB = namedtuple('B', ('spam', 'timeout'))

Strategies = namedtuple('Strategies', ('p', 'q', 'a', 'b'))


class TestSchemaBuilder(object):
    __slots__ = ('segments',)

    def __init__(self):
        self.segments = []

    def publish(self, lower_bound, upper_bound, topic, predicate):
        pass # creates a new trace segment

    def forbid(self, topic, predicate):
        pass # applies a restriction to the current trace segment


class TraceSegment(object):
    __slots__ = ('lower_bound', 'upper_bound', 'topic', 'predicate')
    # FIXME


PublishEvent = namedtuple('PublishEvent',
    ('lower_bound', 'upper_bound', 'topic', 'predicate'))

MsgRestriction = namedtuple('MsgRestriction',
    ('topic', 'predicate'))


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

    def build(self, predicate=None, alias=None, fun_name='cms'):
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
        name = '{}_{}_{}'.format(fun_name,
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
