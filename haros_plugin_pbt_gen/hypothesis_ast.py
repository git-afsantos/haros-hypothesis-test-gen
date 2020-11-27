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
# Statement Classes
################################################################################

from builtins import str
from builtins import object
class Statement(object):
    __slots__ = ()

    @property
    def is_assignment(self):
        return False

    @property
    def is_assumption(self):
        return False

    @property
    def is_loop(self):
        return False

    @property
    def is_block(self):
        return False

    def merge(self, other):
        return False


class Assignment(Statement):
    __slots__ = Statement.__slots__ + ("field", "expression")

    def __init__(self, field, expression):
        # field :: string
        # expression :: string|Expression
        self.field = field
        self.expression = expression

    @property
    def is_assignment(self):
        return True

    def __str__(self):
        return "{} = {}".format(self.field, str(self.expression))


class Assumption(Statement):
    __slots__ = Statement.__slots__ + ("conditions",)

    def __init__(self, conditions=None):
        # conditions :: [FieldCondition]
        self.conditions = conditions if conditions is not None else []

    @property
    def is_assumption(self):
        return True

    @property
    def expression(self):
        return " and ".join(str(c) for c in self.conditions) or "True"

    def merge(self, other):
        if isinstance(other, Assumption):
            self.conditions.extend(other.conditions)
            return True
        return False

    def __str__(self):
        return "assume({})".format(self.expression)


class RangeLoop(Statement):
    __slots__ = Statement.__slots__ + (
        "array", "start", "end", "statement", "excluding", "variable")

    def __init__(self, array, statement, start=0, end=None, excluding=None,
                 var="i"):
        # array :: string
        # statement :: Statement
        self.array = array
        self.statement = statement
        self.start = start
        self.end = end if not end is None else "len({})".format(array)
        self.excluding = tuple(excluding) if excluding is not None else ()
        self.variable = var

    @property
    def is_loop(self):
        return True

    @property
    def expression(self):
        if not self.excluding:
            return "range({}, {})".format(self.start, self.end)
        return "range_excluding({}, {}, {})".format(
            self.start, self.end, self.excluding)

    @property
    def inner_statement(self):
        child = self.statement
        while child.is_loop:
            child = child.statement
        return child

    def merge(self, other):
        if (isinstance(other, RangeLoop) and self.array == other.array
                and self.start == other.start and self.end == other.end
                and self.excluding == other.excluding
                and self.variable == other.variable):
            if self.statement.merge(other.statement):
                return True
            self.statement = StatementBlock([self.statement])
            return self.statement.merge(other.statement)
        return False

    def __str__(self):
        return "for {} in {}:".format(self.variable, self.expression)


class StatementBlock(Statement):
    __slots__ = Statement.__slots__ + ("statements",)

    def __init__(self, statements=None):
        self.statements = list(statements) if statements is not None else []

    @property
    def is_block(self):
        return True

    def merge(self, other):
        if isinstance(other, StatementBlock):
            for st2 in other.statements:
                for st1 in self.statements:
                    if st1.merge(st2):
                        break
                else:
                    self.statements.append(st2)
        else:
            for statement in self.statements:
                if statement.merge(other):
                    break
            else:
                self.statements.append(other)
        return True


################################################################################
# Expression Classes
################################################################################

class Expression(object):
    __slots__ = ()

    def replace(self, old_str, new_str):
        return self

    def __str__(self):
        assert False, "must implement this"


class RandomArray(Expression):
    __slots__ = Expression.__slots__ + ("min_size", "max_size")

    def __init__(self, min_size, max_size, set_size):
        if set_size is not None:
            self.min_size = set_size
            self.max_size = set_size
        else:
            self.min_size = min_size
            self.max_size = max_size

    def __str__(self):
        args = "min_size={}, max_size={}".format(self.min_size, self.max_size)
        return "draw(strategies.lists(strategies.none(), {}))".format(args)


class RandomValue(Expression):
    __slots__ = Expression.__slots__ + ("type_name", "args")

    def __init__(self, type_name, **kwargs):
        self.type_name = type_name
        self.args = kwargs

    def replace(self, old_str, new_str):
        self.args = {key: value.replace(old_str, new_str)
                     for key, value in self.args.items()
                     if value is not None}
        return self

    def __str__(self):
        args = ", ".join("{}={}".format(key, str(value))
                         for key, value in self.args.items()
                         if value is not None)
        return "draw(ros_{}({}))".format(
            self.type_name.replace("/", "_"), args)


class RandomSample(Expression):
    __slots__ = Expression.__slots__ + ("values",)

    def __init__(self, values):
        # values :: [string]
        self.values = values

    def replace(self, old_str, new_str):
        self.values = [v.replace(old_str, new_str) for v in self.values]
        return self

    def __str__(self):
        if self.values:
            values = "({},)".format(", ".join(str(v) for v in self.values))
            return "draw(strategies.sampled_from({}))".format(values)
        return "draw(strategies.sampled_from(()))"


class Literal(Expression):
    __slots__ = Expression.__slots__ + ("value",)

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return str(self.value)


class FieldCondition(Expression):
    __slots__ = Expression.__slots__ + ("field", "operator", "expression")

    def __init__(self, field, operator, expression):
        # field :: string
        # operator :: string
        # expression :: string|Expression
        self.field = field
        self.operator = operator
        self.expression = expression

    def replace(self, old_str, new_str):
        self.field = self.field.replace(old_str, new_str)
        self.expression = self.expression.replace(old_str, new_str)
        return self

    def __str__(self):
        return "{} {} {}".format(
            self.field, self.operator, str(self.expression))


class Disjunction(Expression):
    __slots__ = Expression.__slots__ + ("conditions",)

    def __init__(self, conditions):
        # conditions :: [string|Expression]
        self.conditions = conditions

    def replace(self, old_str, new_str):
        self.conditions = [c.replace(old_str, new_str) for c in self.conditions]
        return self

    def __str__(self):
        return "({})".format(" or ".join(str(c) for c in self.conditions))
