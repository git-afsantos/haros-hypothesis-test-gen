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

from haros.hpl.hpl_ast import HplBinaryOperator, HplLiteral, HplUnaryOperator


###############################################################################
# Utility Functions
###############################################################################

def convert_to_old_format(phi):
    assert phi.is_expression and phi.can_be_bool
    relational = ("=", "!=", "<", "<=", ">", ">=", "in")
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
                    elif expr.operator == "=":
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
                            raise StrategyError(
                                "general LHS operands are not implemented")
                        if not (y.is_accessor or y.is_value):
                            raise StrategyError(
                                "general RHS operands are not implemented")
                        if y.is_accessor:
                            raise StrategyError(
                                "general RHS operands are not implemented")
                        elif y.is_set:
                            for value in y.values:
                                conditions.append(HplBinaryOperator("!=",
                                    x, value))
                        else:
                            assert y.is_range
                            raise StrategyError(
                                "general RHS operands are not implemented")
                    else:
                        raise StrategyError("negation is not implemented")
                else:
                    raise StrategyError("negation is not implemented")
            else:
                if expr.operator == "and":
                    stack.append(expr.operand1)
                    stack.append(expr.operand2)
                elif expr.operator in relational:
                    x = expr.operand1
                    y = expr.operand2
                    if not x.is_accessor:
                        raise StrategyError(
                            "general LHS operands are not implemented")
                    if not (y.is_accessor or y.is_value):
                        raise StrategyError(
                            "general RHS operands are not implemented")
                    conditions.append(expr)
                else:
                    raise StrategyError("operators are not implemented")
    return conditions
