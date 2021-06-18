# -*- coding: utf-8 -*-

#Copyright (c) 2020 André Santos
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

from builtins import str
from collections import namedtuple

from hpl.ast import (
    HplBinaryOperator, HplLiteral, HplUnaryOperator, HplFieldAccess,
    HplArrayAccess, HplThisMessage, HplVarReference
)


###############################################################################
# Utility Functions
###############################################################################

class StrategyError(Exception):
    pass


FakeSet = namedtuple("HplSet", ("values", "is_set", "is_range"))

FakeRange = namedtuple("HplRange",
    ("min_value", "max_value", "exclude_min", "exclude_max",
     "is_set", "is_range"))

def fake_set(values):
    return FakeSet(values, True, False)

def fake_range(lob, upb, excl, excu):
    return FakeRange(lob, upb, excl, excu, False, True)


def convert_to_old_format(phi):
    assert phi.is_expression and phi.can_be_bool
    relational = ("=", "!=", "<", "<=", ">", ">=")
    conditions = []
    stack = [phi]
    while stack:
        expr = stack.pop()
        if expr.is_quantifier:
            raise StrategyError("quantifiers are not implemented")
        elif expr.is_function_call:
            raise StrategyError("function calls are not implemented")
        elif expr.is_accessor:
            expr = HplBinaryOperator("=", expr, HplLiteral("True", True))
            conditions.append(expr)
        elif expr.is_operator:
            if expr.arity == 1:
                assert expr.operator == "not"
                expr = expr.operand
                if expr.is_accessor:
                    conditions.append(HplBinaryOperator("=", expr,
                        HplLiteral("False", False)))
                elif expr.is_operator:
                    if expr.operator == "not":
                        stack.append(expr.operand)
                    elif expr.operator == "or":
                        stack.append(HplUnaryOperator("not", expr.operand1))
                        stack.append(HplUnaryOperator("not", expr.operand2))
                    elif expr.operator == "and":
                        # FIXME: should be an 'or' handled by the template
                        # HAMMER: just choose the first
                        stack.append(HplUnaryOperator("not", expr.operand1))
                    else:
                        x = expr.operand1
                        y = expr.operand2
                        n = False
                        while (not y.is_value and y.is_operator
                                and y.operator == "-"):
                            n = not n
                            y = y.operand
                        if y.is_value and y.is_literal and n:
                            y = HplLiteral("-" + y.token, -y.value)
                        if expr.operator == "=":
                            stack.append(HplBinaryOperator("!=",
                                expr.operand1, expr.operand2))
                        elif expr.operator == "!=":
                            stack.append(HplBinaryOperator("=",
                                expr.operand1, expr.operand2))
                        elif expr.operator == "<":
                            stack.append(HplBinaryOperator(">=",
                                expr.operand1, expr.operand2))
                        elif expr.operator == "<=":
                            stack.append(HplBinaryOperator(">",
                                expr.operand1, expr.operand2))
                        elif expr.operator == ">":
                            stack.append(HplBinaryOperator("<=",
                                expr.operand1, expr.operand2))
                        elif expr.operator == ">=":
                            stack.append(HplBinaryOperator("<",
                                expr.operand1, expr.operand2))
                        elif expr.operator == "in":
                            x = expr.operand1
                            y = expr.operand2
                            if not x.is_accessor:
                                if not (x.is_function_call and x.function == "len"):
                                    raise StrategyError(
                                        "general LHS operands are not implemented")
                            if not (y.is_accessor or y.is_value):
                                raise StrategyError(
                                    "general RHS operands are not implemented")
                            if y.is_accessor:
                                raise StrategyError(
                                    "general RHS operands are not implemented")
                            elif y.is_set:
                                vs = []
                                for v in y.values:
                                    n = False
                                    while (not v.is_value and v.is_operator
                                            and v.operator == "-"):
                                        n = not n
                                        v = v.operand
                                    if v.is_value and v.is_literal and n:
                                        v = HplLiteral("-" + v.token, -v.value)
                                    vs.append(v)
                                y = fake_set(vs)
                                for value in y.values:
                                    conditions.append(HplBinaryOperator("!=",
                                        x, value))
                            else:
                                assert y.is_range
                                # FIXME
                                vmin = y.min_value
                                n = False
                                while (not vmin.is_value and vmin.is_operator
                                        and vmin.operator == "-"):
                                    n = not n
                                    vmin = vmin.operand
                                if vmin.is_value and vmin.is_literal and n:
                                    vmin = HplLiteral("-" + vmin.token, -vmin.value)
                                conditions.append(HplBinaryOperator("<",
                                        x, vmin))
                        else:
                            raise StrategyError("negation is not implemented")
                else:
                    raise StrategyError("negation is not implemented")
            else:
                if expr.operator == "and":
                    stack.append(expr.operand1)
                    stack.append(expr.operand2)
                elif expr.operator == "or":
                    # FIXME: 'or' should be handled at runtime in the template
                    # HAMMER: just choose the first operand
                    stack.append(expr.operand1)
                elif expr.operator in relational:
                    x = expr.operand1
                    y = expr.operand2
                    n = False
                    if not x.is_accessor:
                        if not (x.is_function_call and x.function == "len"):
                            raise StrategyError(
                                "general LHS operands are not implemented")
                    if not (y.is_accessor or y.is_value or
                            (y.is_operator and y.operator == "-")):
                        raise StrategyError(
                            "general RHS operands are not implemented: "
                            + str(phi))
                    while not y.is_value and y.is_operator:
                        assert y.operator == "-"
                        n = not n
                        y = y.operand
                    if y.is_value and y.is_literal and n:
                        y = HplLiteral("-" + y.token, -y.value)
                        conditions.append(
                            HplBinaryOperator(expr.operator, x, y))
                    else:
                        conditions.append(expr)
                elif expr.operator == "in":
                    x = expr.operand1
                    y = expr.operand2
                    if not x.is_accessor:
                        if not (x.is_function_call and x.function == "len"):
                            raise StrategyError(
                                "general LHS operands are not implemented")
                    if not (y.is_accessor or y.is_value):
                        raise StrategyError(
                            "general RHS operands are not implemented")
                    if y.is_value:
                        if y.is_set:
                            vs = []
                            for v in y.values:
                                n = False
                                while not v.is_value and v.is_operator:
                                    assert v.operator == "-"
                                    n = not n
                                    v = v.operand
                                if v.is_value and v.is_literal and n:
                                    v = HplLiteral("-" + v.token, -v.value)
                                vs.append(v)
                            y = fake_set(vs)
                        else:
                            vmin = y.min_value
                            n = False
                            while not vmin.is_value and vmin.is_operator:
                                assert vmin.operator == "-"
                                n = not n
                                vmin = vmin.operand
                            if vmin.is_value and vmin.is_literal and n:
                                vmin = HplLiteral("-" + vmin.token, -vmin.value)
                            vmax = y.max_value
                            n = False
                            while not vmax.is_value and vmax.is_operator:
                                assert vmax.operator == "-"
                                n = not n
                                vmax = vmax.operand
                            if vmax.is_value and vmax.is_literal and n:
                                vmax = HplLiteral("-" + vmax.token, -vmax.value)
                            y = fake_range(vmin, vmax, y.exclude_min, y.exclude_max)
                    conditions.append(expr)
                else:
                    raise StrategyError("operators are not implemented")
    return conditions


def replace_base_msg(accessor, repl=None):
    assert accessor.is_accessor
    stack = []
    obj = accessor
    while not obj.is_value and obj.is_accessor:
        stack.append(obj)
        obj = obj.message
    assert obj.is_value
    if obj.is_this_msg:
        if repl is None:
            return accessor
        obj = HplVarReference("@" + repl)
    else:
        assert obj.is_variable
        if repl is None:
            obj = HplThisMessage()
        else:
            if repl == obj.name:
                return accessor
            obj = HplVarReference("@" + repl)
    while stack:
        op = stack.pop()
        if op.is_field:
            obj = HplFieldAccess(obj, op.field)
        else:
            assert op.is_indexed
            obj = HplArrayAccess(obj, op.index)
    return obj
