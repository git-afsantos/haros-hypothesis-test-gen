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

from builtins import map
from builtins import object
from builtins import range # Python 2 and 3: forward-compatible


###############################################################################
# Field Selector
###############################################################################

class Accessor(object):
    __slots__ = ("field_name", "ros_type")

    def __init__(self, field_name, type_token):
        self.field_name = field_name
        self.ros_type = type_token

    @property
    def is_dynamic(self):
        return False

    @property
    def is_range(self):
        return False

    def matches(self, field_name):
        return self.field_name == field_name

    def __str__(self):
        return self.field_name

    def __repr__(self):
        return "{}({}, {})".format(
            type(self).__name__, self.field_name, repr(self.ros_type))


class RangeAccessor(Accessor):
    __slots__ = Accessor.__slots__

    def __init__(self, field_name, type_token):
        raise NotImplementedError()

    @property
    def is_range(self):
        return True


class DynamicAccessor(Accessor):
    __slots__ = Accessor.__slots__ + ("predicate",)

    def __init__(self, field_name, type_token):
        assert not type_token.is_array
        Accessor.__init__(self, field_name, type_token)
        self.predicate = self._make_predicate(field_name)

    @property
    def is_dynamic(self):
        return True

    def matches(self, key):
        return self.predicate(key)

    def _make_predicate(self, field_name):
        assert field_name.startswith("*")
        if field_name == "*":
            return _universal
        star, indices = field_name.split("\\")
        indices = list(map(int, indices.split(",")))
        return self._all_except(indices)

    def _all_except(self, indices):
        def predicate(key):
            return key not in indices
        return predicate


class Selector(object):
    __slots__ = ("expression", "base_type", "accessors")

    _DYNAMIC = "*"

    def __init__(self, field_expr, ros_type):
        self.expression = field_expr
        self.base_type = ros_type
        accessors = []
        parts = field_expr.replace("]", "").replace("[", ".").split(".")
        if not parts:
            raise ValueError(field_expr)
        type_token = ros_type
        for field_name in parts:
            if type_token.is_array:
                accessor = self._array_access(field_name, type_token)
                type_token = accessor.ros_type
                accessors.append(accessor)
            elif not type_token.is_primitive:
                type_token = type_token.fields[field_name]
                accessor = Accessor(field_name, type_token)
                accessors.append(accessor)
            else:
                raise KeyError(field_name)
        self.accessors = tuple(accessors)

    @property
    def field_name(self):
        return self.accessors[-1].field_name

    @property
    def ros_type(self):
        return self.accessors[-1].ros_type

    @property
    def is_dynamic(self):
        for accessor in self.accessors:
            if accessor.is_dynamic:
                return True
        return False

    @property
    def is_array_field(self):
        return (len(self.accessors) >= 2
                and self.accessors[-2].ros_type.is_array)

    def subselect(self, n):
        if n <= 0:
            raise IndexError(n)
        if n >= len(self.accessors):
            return self
        parts = [self.accessors[0].field_name]
        array = self.accessors[0].ros_type.is_array
        for i in range(1, n):
            f = self.accessors[i]
            if array:
                parts.append("[")
                parts.append(f.field_name)
                parts.append("]")
            else:
                parts.append(".")
                parts.append(f.field_name)
            array = f.ros_type.is_array
        selector = Selector("".join(parts), self.base_type)
        return selector

    def _array_access(self, field_name, array_type):
        if field_name.startswith(self._DYNAMIC):
            return DynamicAccessor(field_name, array_type.type_token)
        try:
            index = int(field_name, 10)
        except ValueError as e:
            raise KeyError(field_name)
        if not array_type.contains_index(index):
            raise KeyError(field_name)
        return Accessor(field_name, array_type.type_token)

    def __iter__(self):
        return iter(self.accessors)

    def __eq__(self, other):
        if not isinstance(other, Selector):
            return False
        return (self.expression == other.expression
                and self.base_type == other.base_type)

    def __hash__(self):
        return 31 * hash(self.expression) + hash(self.base_type)

    def __str__(self):
        return self.expression

    def __repr__(self):
        return "Selector({}, {})".format(self.expression, repr(self.base_type))


###############################################################################
# Predicates
###############################################################################

def _universal(key):
    return True
