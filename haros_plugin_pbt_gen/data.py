# -*- coding: utf-8 -*-

#Copyright (c) 2018 André Santos
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
# Notes
###############################################################################

"""
## Ideal Reference Handling ##

DataFieldGenerator:
    eq: Reference(Data, finalized, no loops)
    neq: [Reference(Data, finalized, loops allowed)]
    in: [Reference(Data, finalized, loops allowed)]
    lt: [Reference(Data, finalized, loops allowed)]
    gt: [Reference(Data, finalized, loops allowed)]

CompositeFieldGenerator:
    eq: Reference(Composite, initialized, no loops)
    neq: [Reference(Composite, finalized, loops allowed)]
    in: [Reference(Composite, initialized, loops allowed)]

ArrayFieldGenerator:
    eq: Reference(Array, initialized, no loops)
    neq: [Reference(Array, finalized, loops allowed)]
    in: [Reference(Array, initialized, loops allowed)]
"""


###############################################################################
# Imports
###############################################################################

from builtins import map
from builtins import str
from past.builtins import basestring
from builtins import object
from builtins import range # Python 2 and 3: forward-compatible

from .hypothesis_ast import (
    Assignment, Assumption, Disjunction, FieldCondition, RandomArray,
    RandomSample, RandomValue, RangeLoop
)
from .selectors import Selector


################################################################################
# Custom Exception Types
################################################################################

class MessageFilterError(Exception):
    pass

class InvalidFieldOperatorError(MessageFilterError):
    pass

class ContradictionError(MessageFilterError):
    pass

class CyclicDependencyError(MessageFilterError):
    pass


################################################################################
# Public Interface: Top-level Strategy Generator
################################################################################

# Doing this in two passes leads to slightly less complex code, since
# multi-selectors can store all satisfying generators from the start.
# Their implementation becomes a simple view/forward object.
# Otherwise, references have to store the selectors and run the whole logic
# from the root everytime they are accessed, or an explicit call is needed
# to resolve and cache all references (e.g., `update()`).
# In addition, multi-selectors would have to create an additional generator
# to buffer constraints, which would be applied to new concrete fields
# added afterwards.

class MessageStrategyGenerator(object):
    __slots__ = ("root", "args", "_build_number")

    def __init__(self, type_token):
        self.root = RootFieldGenerator(type_token)
        self.args = [] # [string] - order is important
        self._build_number = 0

    def ensure_generator(self, selector):
        # At this stage we do not care about dynamic selectors yet.
        # We are only creating static ones, so that they are available
        # later on for dynamic selectors.
        current = self.root
        for accessor in selector:
            if accessor.is_dynamic:
                return
            # current.access() creates the generator lazily
            current = current.access(accessor)

    def build(self):
        statements = []
        self._build_number += 1
        queue = self._init_build_queue()
        while queue:
            queue = self._build_statements(statements, queue)
        return statements

    def make_msg_arg(self, name, selector):
        arg_name = "msg_" + name
        if arg_name not in self.args:
            self.args.append(arg_name)
        if not isinstance(selector, Selector):
            raise TypeError("expected Selector, got " + type(selector).__name__)
        if selector.is_dynamic:
            raise ValueError("dynamic selectors are not supported: "
                             + selector.expression)
        return _ArgReference(arg_name, selector)

    def set_eq(self, selector, value):
        field = self._select(selector)
        if isinstance(value, Selector):
            other = self._select(value, allow_multiple=False, invalidate=True)
            value = _LocalReference(other, FieldGenerator.INITIALIZED)
        elif not isinstance(value, _ArgReference):
            value = _LiteralWrapper(value)
        field.eq(value)

    def set_neq(self, selector, value):
        field = self._select(selector)
        if isinstance(value, Selector):
            other = self._select(value)
            value = _LocalReference(other, FieldGenerator.FINALIZED)
        elif not isinstance(value, _ArgReference):
            value = _LiteralWrapper(value)
        field.neq(value)

    def set_lt(self, selector, value):
        field = self._select(selector)
        assert field.ros_type.is_number
        if isinstance(value, Selector):
            other = self._select(value, reducer="max", invalidate=True)
            assert other.ros_type.is_number
            value = _LocalReference(other, FieldGenerator.FINALIZED)
        elif not isinstance(value, _ArgReference):
            value = _LiteralWrapper(value)
        field.lt(value)

    def set_lte(self, selector, value):
        field = self._select(selector)
        assert field.ros_type.is_number
        if isinstance(value, Selector):
            other = self._select(value, reducer="max", invalidate=True)
            assert other.ros_type.is_number
            value = _LocalReference(other, FieldGenerator.FINALIZED)
        elif not isinstance(value, _ArgReference):
            value = _LiteralWrapper(value)
        field.lte(value)

    def set_gt(self, selector, value):
        field = self._select(selector)
        assert field.ros_type.is_number
        if isinstance(value, Selector):
            other = self._select(value, reducer="min", invalidate=True)
            assert other.ros_type.is_number
            value = _LocalReference(other, FieldGenerator.FINALIZED)
        elif not isinstance(value, _ArgReference):
            value = _LiteralWrapper(value)
        field.gt(value)

    def set_gte(self, selector, value):
        field = self._select(selector)
        assert field.ros_type.is_number
        if isinstance(value, Selector):
            other = self._select(value, reducer="min", invalidate=True)
            assert other.ros_type.is_number
            value = _LocalReference(other, FieldGenerator.FINALIZED)
        elif not isinstance(value, _ArgReference):
            value = _LiteralWrapper(value)
        field.gte(value)

    def set_in(self, selector, values):
        field = self._select(selector)
        new_values = []
        for value in values:
            if isinstance(value, Selector):
                other = self._select(value, allow_multiple=False,
                                     invalidate=True)
                value = _LocalReference(other, FieldGenerator.INITIALIZED)
            elif not isinstance(value, _ArgReference):
                value = _LiteralWrapper(value)
            new_values.append(value)
        field.in_set(new_values)

    def set_not_in(self, selector, values):
        field = self._select(selector)
        new_values = []
        for value in values:
            if isinstance(value, Selector):
                other = self._select(value, allow_multiple=False)
                value = _LocalReference(other, FieldGenerator.FINALIZED)
            elif not isinstance(value, _ArgReference):
                value = _LiteralWrapper(value)
            new_values.append(value)
        field.not_in(new_values)

    def set_not_in_range(self, selector, min_value, max_value,
                         exclude_min=False, exclude_max=False):
        field = self._select(selector)
        if isinstance(min_value, Selector):
            other = self._select(min_value, allow_multiple=False)
            min_value = _LocalReference(other, FieldGenerator.FINALIZED)
        elif not isinstance(min_value, _ArgReference):
            min_value = _LiteralWrapper(min_value)
        if isinstance(max_value, Selector):
            other = self._select(max_value, allow_multiple=False)
            max_value = _LocalReference(other, FieldGenerator.FINALIZED)
        elif not isinstance(max_value, _ArgReference):
            max_value = _LiteralWrapper(max_value)
        field.not_in_range(min_value, max_value, exclude_min, exclude_max)

    def set_attr_eq(self, selector, value, attr):
        assert selector.ros_type.is_array
        field = self._select(selector)
        value = _LiteralWrapper(value)
        field.eq(value, attr=attr)

    def set_attr_neq(self, selector, value, attr):
        assert selector.ros_type.is_array
        field = self._select(selector)
        value = _LiteralWrapper(value)
        field.neq(value, attr=attr)

    def set_attr_lt(self, selector, value, attr):
        assert selector.ros_type.is_array
        field = self._select(selector)
        value = _LiteralWrapper(value)
        field.lt(value, attr=attr)

    def set_attr_lte(self, selector, value, attr):
        assert selector.ros_type.is_array
        field = self._select(selector)
        value = _LiteralWrapper(value)
        field.lte(value, attr=attr)

    def set_attr_gt(self, selector, value, attr):
        assert selector.ros_type.is_array
        field = self._select(selector)
        value = _LiteralWrapper(value)
        field.gt(value, attr=attr)

    def set_attr_gte(self, selector, value, attr):
        assert selector.ros_type.is_array
        field = self._select(selector)
        value = _LiteralWrapper(value)
        field.gte(value, attr=attr)

    def _select(self, selector, allow_multiple=True, reducer=None,
                invalidate=False):
        multiple = False
        current = self.root
        for accessor in selector:
            if invalidate and current.strategy.is_default:
                if not current.ros_type.is_array:
                    current.strategy = _NoopStrategy(current._ready_ref)
            current = current.access(accessor)
            if accessor.is_dynamic or accessor.is_range:
                assert allow_multiple
                multiple = True
        assert current is not self.root
        if multiple:
            current.reducer = reducer
        return current

    def _init_build_queue(self):
        queue = []
        fields = list(self.root.fields.values())
        while fields:
            field = fields.pop(0)
            queue.append(field.strategy)
            queue.extend(field.assumptions)
            if not field.is_data_field:
                if field.ros_type.is_array:
                    fields.append(field.by_default)
                    fields.extend(field.fields.values())
                else:
                    if field.is_default:
                        field.noop_tree()
                    elif field.strategy.is_default:
                        field.cautious_noop_tree()
                    # this is needed so we do not miss assumptions
                    fields.extend(field.fields.values())
        return queue

    def _build_statements(self, results, queue):
        b = self._build_number
        new_queue = []
        progress = False
        for builder in queue:
            assert builder.build_number != b, "stamp only when done"
            if builder.available(b):
                builder.build_number = b
                progress = True
                statement = builder.build()
                if (statement is not None
                        and (not results or not results[-1].merge(statement))):
                    results.append(statement)
            else:
                new_queue.append(builder)
        if not progress:
            raise CyclicDependencyError(queue)
        return new_queue


################################################################################
# Internal Structures: Basic (Data) Field Generator
################################################################################

# A FieldGenerator is composed of multiple statements (initialization,
# assumptions, ...) and each statement has its own dependencies (references
# to other local/external fields) so that they can be sorted individually.
# This maximizes flexibility, and results in code that is closer to what a
# human would write, knowing in advance what each statement needs.
# Internally, the FieldGenerator can be seen as a sort of state machine.
# When generating code, it changes its state as the requirements of each
# statement are satisfied and the statements are processed.

class FieldGenerator(object):
    __slots__ = ("expression", "ros_type", "parent", "strategy", "assumptions",
                 "reference_count", "_ready_ref", "_init_ref", "ranged",
                 "_loop_context")

    PENDING = 0 # waiting for the parent to be initialized
    READY = 1 # the parent is available, this can be initialized
    INITIALIZED = 2 # the field has a value, but there is more to do
    FINALIZED = 3 # the field and all subfields are fully processed

    def __init__(self, expression, type_token, parent, ranged=False,
                 _loop_context=None):
        self.expression = expression
        self.ros_type = type_token
        self.parent = parent
        # FIXME I think reference_count is not needed
        self.reference_count = 0 # how many references there are to this field
        self.assumptions = []
        self._ready_ref = _LocalReference(self, self.READY)
        self._init_ref = _LocalReference(self, self.INITIALIZED)
        self.strategy = _DefaultStrategy(self._ready_ref)
        self.ranged = ranged
        self._loop_context = _loop_context or parent._loop_context

    @property
    def is_singular(self):
        return True

    @property
    def is_data_field(self):
        return True

    @property
    def requires_loop(self):
        return self.ranged or self.parent.requires_loop

    def state(self, build_number):
        if self.strategy.build_number == build_number:
            for assumption in self.assumptions:
                if assumption.build_number != build_number:
                    return self.INITIALIZED
            return self.FINALIZED
        if not self.parent._initialized(build_number):
            return self.PENDING
        return self.READY

    def access(self, accessor):
        raise KeyError(accessor.field_name)

    def eq(self, value):
        if not self.strategy.is_constant:
            self.strategy = _EqualTo(self._ready_ref, value)

    def neq(self, value):
        if self.strategy.is_enum:
            if value in self.strategy.values:
                self.strategy.values.remove(value)
            if len(self.strategy.values) <= 0:
                raise ContradictionError("{} != {}".format(
                    self.expression, value))
        self.assumptions.append(_Assumption(self._init_ref, value, "!="))

    def lt(self, value):
        assert self.ros_type.is_number
        if self.strategy.is_default or self.strategy.is_noop:
            self.strategy = _NumberInterval(self._ready_ref)
        if self.strategy.is_random_number:
            self.strategy.max_values.add(value)
        self.assumptions.append(_Assumption(self._init_ref, value, "<"))

    def lte(self, value):
        assert self.ros_type.is_number
        if self.strategy.is_default or self.strategy.is_noop:
            self.strategy = _NumberInterval(self._ready_ref)
        if self.strategy.is_random_number:
            self.strategy.max_values.add(value)
        self.assumptions.append(_Assumption(self._init_ref, value, "<="))

    def gt(self, value):
        assert self.ros_type.is_number
        if self.strategy.is_default or self.strategy.is_noop:
            self.strategy = _NumberInterval(self._ready_ref)
        if self.strategy.is_random_number:
            self.strategy.min_values.add(value)
        self.assumptions.append(_Assumption(self._init_ref, value, ">"))

    def gte(self, value):
        assert self.ros_type.is_number
        if self.strategy.is_default or self.strategy.is_noop:
            self.strategy = _NumberInterval(self._ready_ref)
        if self.strategy.is_random_number:
            self.strategy.min_values.add(value)
        self.assumptions.append(_Assumption(self._init_ref, value, ">="))

    def in_set(self, values):
        if self.strategy.is_enum:
            common = set(self.strategy.values) & set(values)
            for assumption in self.assumptions:
                if assumption.operator == "!=":
                    if assumption.value in common:
                        common.remove(assumption.value)
            if len(common) <= 0:
                raise ContradictionError("{} in {}".format(
                    self.expression, values))
            self.strategy = _SampledFrom(self._ready_ref, common)
        elif not self.strategy.is_constant:
            new_values = list(values)
            for assumption in self.assumptions:
                if assumption.operator == "!=":
                    if assumption.value in new_values:
                        new_values.remove(assumption.value)
            if len(new_values) <= 0:
                raise ContradictionError("{} in {}".format(
                    self.expression, values))
            self.strategy = _SampledFrom(self._ready_ref, new_values)

    def not_in(self, values):
        for value in values:
            self.neq(value)

    def not_in_range(self, min_value, max_value, exclude_min, exclude_max):
        assert self.ros_type.is_number
        gt = ">=" if exclude_max else ">"
        lt = "<=" if exclude_min else "<"
        self.assumptions.append(_Or(
            _Assumption(self._init_ref, min_value, lt),
            _Assumption(self._init_ref, max_value, gt)))

    def _initialized(self, build_number):
        # This is needed in order to avoid infinite recursion with state(),
        # where a CompositeFieldGenerator depends both on its parent and its
        # children (READY and FINALIZED, respectively).
        return self.strategy.build_number == build_number

    def _template(self):
        return "msg." + self.expression


################################################################################
# Composite Field Generators (Embedded Messages)
################################################################################

class CompositeFieldGenerator(FieldGenerator):
    __slots__ = FieldGenerator.__slots__ + ("fields",)

    def __init__(self, expression, type_token, parent, ranged=False,
                 _loop_context=None):
        FieldGenerator.__init__(self, expression, type_token, parent,
                                ranged=ranged, _loop_context=_loop_context)
        self.fields = {}
        for field_name, ros_type in type_token.fields.items():
            expr = ".".join((expression, field_name))
            self.fields[field_name] = _make_generator(expr, ros_type, self)

    @property
    def is_data_field(self):
        return False

    @property
    def is_default(self):
        if not self.strategy.is_default:
            return False
        fields = list(self.fields.values())
        while fields:
            field = fields.pop(0)
            if not field.strategy.is_default:
                return False
            if not field.is_data_field:
                fields.extend(field._children())
        return True

    def state(self, build_number):
        if self.strategy.build_number != build_number:
            if not self.parent._initialized(build_number):
                return self.PENDING
            return self.READY
        for assumption in self.assumptions:
            if assumption.build_number != build_number:
                return self.INITIALIZED
        for field in self.fields.values():
            if field.state(build_number) != self.FINALIZED:
                return self.INITIALIZED
        return self.FINALIZED

    def access(self, accessor):
        return self.fields[accessor.field_name]

    def lt(self, value):
        raise InvalidFieldOperatorError("<")

    def lte(self, value):
        raise InvalidFieldOperatorError("<=")

    def gt(self, value):
        raise InvalidFieldOperatorError(">")

    def gte(self, value):
        raise InvalidFieldOperatorError(">=")

    def noop_tree(self):
        fields = list(self.fields.values())
        while fields:
            field = fields.pop(0)
            assert field.strategy.is_default
            field.strategy = _NoopStrategy(field._ready_ref)
            if not field.is_data_field:
                fields.extend(field._children())

    def cautious_noop_tree(self):
        fields = list(self.fields.values())
        while fields:
            field = fields.pop(0)
            if field.strategy.is_default:
                field.strategy = _NoopStrategy(field._ready_ref)
            if not field.is_data_field:
                fields.extend(field._children())

    def _children(self):
        return tuple(self.fields.values())


class RootFieldGenerator(FieldGenerator):
    __slots__ = ("ros_type", "fields", "strategy", "reference_count",
                 "_loop_context")

    def __init__(self, type_token):
        assert not type_token.is_primitive
        self.ros_type = type_token
        self.fields = {}
        self._loop_context = _LoopContext(())
        for field_name, ros_type in type_token.fields.items():
            self.fields[field_name] = _make_generator(
                    "msg." + field_name, ros_type, self)
        self.reference_count = 0
        self.strategy = _NoopStrategy(_LocalReference(self, self.READY))

    @property
    def is_data_field(self):
        return False

    @property
    def requires_loop(self):
        return False

    def state(self, build_number):
        for field in self.fields.values():
            if field.state(build_number) != self.FINALIZED:
                return self.INITIALIZED
        return self.FINALIZED

    def access(self, accessor):
        return self.fields[accessor.field_name]

    def eq(self, value):
        raise InvalidFieldOperatorError("=")

    def neq(self, value):
        raise InvalidFieldOperatorError("!=")

    def lt(self, value):
        raise InvalidFieldOperatorError("<")

    def lte(self, value):
        raise InvalidFieldOperatorError("<=")

    def gt(self, value):
        raise InvalidFieldOperatorError(">")

    def gte(self, value):
        raise InvalidFieldOperatorError(">=")

    def in_set(self, values):
        raise InvalidFieldOperatorError("in")

    def not_in(self, values):
        raise InvalidFieldOperatorError("not in")

    def _initialized(self, build_number):
        return True

    def _children(self):
        return tuple(self.fields.values())

    def _template(self):
        return "msg"


################################################################################
# Arrays and Multi-Field Generators
################################################################################

# TODO implement range/interval logic for arrays.
# They should start with a generator that applies to [0:length].
# When a static field is added, the interval breaks down into multiple
# intervals (e.g. adding [2] changes the interval into [0:2] + [3:length]).

class ArrayFieldGenerator(FieldGenerator):
    __slots__ = FieldGenerator.__slots__ + ("set_length", "min_length",
        "max_length", "neq_length", "by_default", "fields")

    _ATTRS = ("len",)

    _UNK_ATTR = "unknown array attribute: '{}'"

    def __init__(self, expression, type_token, parent):
        FieldGenerator.__init__(self, expression, type_token, parent)
        self.set_length = type_token.length
        self.min_length = type_token.length or 0
        self.max_length = type_token.length
        self.neq_length = set()
        self.by_default = _make_generator(expression, type_token.type_token,
                                          self, nest=True)
        self.by_default.ranged = True
        self.fields = {}

    @property
    def is_data_field(self):
        return False

    def state(self, build_number):
        if self.strategy.build_number != build_number:
            if not self.parent._initialized(build_number):
                return self.PENDING
            return self.READY
        for assumption in self.assumptions:
            if assumption.build_number != build_number:
                return self.INITIALIZED
        if self.by_default.state(build_number) != self.FINALIZED:
            return self.INITIALIZED
        for field in self.fields.values():
            if field.state(build_number) != self.FINALIZED:
                return self.INITIALIZED
        return self.FINALIZED

    def access(self, accessor):
        if accessor.is_dynamic:
            return self._get_multifield(accessor)
        elif accessor.is_range:
            raise NotImplementedError()
        else:
            return self._get_static_field(accessor)

    def eq(self, value, attr=None):
        if attr is None:
            return FieldGenerator.eq(self, value)
        if attr == "len":
            assert isinstance(value, _LiteralWrapper)
            n = value.value
            if self.set_length is None:
                if self.min_length > n:
                    msg = "cannot set {} length to {} and >={}"
                    msg = msg.format(self.expression, n, self.min_length)
                    raise ValueError(msg)
                if self.max_length is not None and self.max_length < n:
                    msg = "cannot set {} length to {} and <={}"
                    msg = msg.format(self.expression, n, self.max_length)
                    raise ValueError(msg)
                if n in self.neq_length:
                    msg = "cannot set {} length to {} and !={}"
                    msg = msg.format(self.expression, n, n)
                    raise ValueError(msg)
                self.set_length = self.min_length = self.max_length = n
            else:
                if self.set_length != n:
                    raise ValueError("cannot set {} length to {} and {}".format(
                        self.expression, self.set_length, n))
        else:
            raise ValueError(self._UNK_ATTR.format(attr))

    def neq(self, value, attr=None):
        if attr is None:
            return FieldGenerator.neq(self, value)
        if attr == "len":
            assert isinstance(value, _LiteralWrapper)
            n = value.value
            if self.set_length == n:
                msg = "cannot set {} length to {} and !={}"
                msg = msg.format(self.expression, n, self.set_length)
                raise ValueError(msg)
            self.neq_length.add(n)
            self.assumptions.append(_Assumption(
                self._init_ref, value, "!=", fun="len"))
        else:
            raise ValueError(self._UNK_ATTR.format(attr))

    def lt(self, value, attr=None):
        if attr not in self._ATTRS:
            raise InvalidFieldOperatorError("<")
        if attr == "len":
            assert isinstance(value, _LiteralWrapper)
            n = value.value
            if n == 0:
                msg = "cannot set {} length to <0".format(self.expression)
                raise ValueError(msg)
            if self.min_length is not None and self.min_length >= n:
                msg = "cannot set {} length to <{} and >={}"
                msg = msg.format(self.expression, n, self.min_length)
                raise ValueError(msg)
            if self.max_length is None or self.max_length >= n:
                self.max_length = n - 1
                self.assumptions.append(_Assumption(
                    self._init_ref, value, "<", fun="len"))
        else:
            raise ValueError(self._UNK_ATTR.format(attr))

    def lte(self, value, attr=None):
        if attr not in self._ATTRS:
            raise InvalidFieldOperatorError("<=")
        if attr == "len":
            assert isinstance(value, _LiteralWrapper)
            n = value.value
            if self.min_length is not None and self.min_length > n:
                msg = "cannot set {} length to <={} and >={}"
                msg = msg.format(self.expression, n, self.min_length)
                raise ValueError(msg)
            if self.max_length is None or self.max_length > n:
                self.max_length = n
                self.assumptions.append(_Assumption(
                    self._init_ref, value, "<=", fun="len"))
        else:
            raise ValueError(self._UNK_ATTR.format(attr))

    def gt(self, value, attr=None):
        if attr not in self._ATTRS:
            raise InvalidFieldOperatorError(">")
        if attr == "len":
            assert isinstance(value, _LiteralWrapper)
            n = value.value
            if self.max_length is not None and self.max_length <= n:
                msg = "cannot set {} length to >{} and <={}"
                msg = msg.format(self.expression, n, self.max_length)
                raise ValueError(msg)
            if self.min_length is None or self.min_length <= n:
                self.min_length = n + 1
                self.assumptions.append(_Assumption(
                    self._init_ref, value, ">", fun="len"))
        else:
            raise ValueError(self._UNK_ATTR.format(attr))

    def gte(self, value, attr=None):
        if attr not in self._ATTRS:
            raise InvalidFieldOperatorError(">=")
        if attr == "len":
            assert isinstance(value, _LiteralWrapper)
            n = value.value
            if self.max_length is not None and self.max_length < n:
                msg = "cannot set {} length to >={} and <={}"
                msg = msg.format(self.expression, n, self.max_length)
                raise ValueError(msg)
            if self.min_length is None or self.min_length < n:
                self.min_length = n
                self.assumptions.append(_Assumption(
                    self._init_ref, value, ">=", fun="len"))
        else:
            raise ValueError(self._UNK_ATTR.format(attr))

    def _get_multifield(self, accessor):
        # NOTE: This assumes that all static generators are already present.
        # If this assumption is to be removed, then the accessor must be stored
        # and a buffer generator must be created, so that all constraints are
        # saved to apply later on new concrete fields.
        # FIXME: assuming only "for all" now.
        fields = list(gen for key, gen in self.fields.items()
                       if accessor.matches(key))
        fields.append(self.by_default)
        return MultiGeneratorView(tuple(fields))

    def _get_static_field(self, accessor):
        field_name = accessor.field_name
        try:
            index = int(field_name, 10)
        except ValueError as e:
            raise KeyError(field_name)
        if index < 0:
            raise IndexError(field_name)
        if self.ros_type.is_fixed_length:
            if index >= self.ros_type.length:
                raise IndexError(field_name)
        elif index >= self.min_length:
            self.min_length = index + 1
        field = self.fields.get(index)
        if field is None:
            expr = "".join((self.expression, "[", field_name, "]"))
            field = _make_generator(expr, self.ros_type.type_token, self)
            self.fields[index] = field
        return field

    def _children(self):
        children = [self.by_default]
        children.extend(self.fields.values())
        return children


# FIXME
class RangeGeneratorView(FieldGenerator):
    __slots__ = ("array", "generator")

    def __init__(self, array, type_token):
        self.array = array
        self.generator = _make_generator(array.expression, type_token, array)

    @property
    def is_singular(self):
        return False

    @property
    def is_loop(self):
        return True

    @property
    def is_data_field(self):
        return self.generator.is_data_field

    def state(self, build_number):
        return self.generator.state(build_number)

    def access(self, accessor):
        return MultiGeneratorView.from_accessor(accessor, self.fields)

    def eq(self, value):
        return self.generator.eq(value)

    def neq(self, value):
        return self.generator.neq(value)

    def lt(self, value):
        return self.generator.lt(value)

    def lte(self, value):
        return self.generator.lte(value)

    def gt(self, value):
        return self.generator.gt(value)

    def gte(self, value):
        return self.generator.gte(value)

    def in_set(self, values):
        return self.generator.in_set(values)

    def not_in(self, values):
        return self.generator.not_in(values)

    def _loop(self):
        return "RangeExcluding(len({}), ({},))".format(
            str(self.field), ", ".join(str(i) for i in self.array.fields))

    def _template(self):
        fields = ", ".join(field._template() for field in self.fields)
        if self.reducer is not None:
            return "{}({})".format(self.reducer, fields)
        return "({},)".format(fields)


class MultiGeneratorView(FieldGenerator):
    """
    A class to aggregate multiple generators.
    It is mostly intended to work with dynamic selectors, i.e.,
    index patterns that are not fully determined from the start.
    Example: the 'universal' selector, selects all indices from 0 to the
    length of the array.
    """

    __slots__ = ("fields", "ros_type", "reducer")

    def __init__(self, fields, reducer=None):
        ros_types = set(f.ros_type for f in fields)
        assert len(ros_types) <= 1
        self.fields = fields
        self.ros_type = None if not fields else fields[0].ros_type
        self.reducer = reducer

    @classmethod
    def from_accessor(cls, accessor, fields):
        new_fields = []
        for field in fields:
            new = field.access(accessor)
            if isinstance(new, MultiGeneratorView):
                new_fields.extend(new.fields)
            else:
                new_fields.append(new)
        return MultiGeneratorView(new_fields)

    @property
    def is_singular(self):
        return False

    @property
    def is_loop(self):
        return False

    @property
    def is_data_field(self):
        return all(field.is_data_field for field in self.fields)

    def state(self, build_number):
        return min(field.state(build_number) for field in self.fields)

    def access(self, accessor):
        return MultiGeneratorView.from_accessor(accessor, self.fields)

    def eq(self, value):
        for field in self.fields:
            field.eq(value)

    def neq(self, value):
        for field in self.fields:
            field.neq(value)

    def lt(self, value):
        for field in self.fields:
            field.lt(value)

    def lte(self, value):
        for field in self.fields:
            field.lte(value)

    def gt(self, value):
        for field in self.fields:
            field.gt(value)

    def gte(self, value):
        for field in self.fields:
            field.gte(value)

    def in_set(self, values):
        for field in self.fields:
            field.in_set(values)

    def not_in(self, values):
        for field in self.fields:
            field.not_in(values)

    def _template(self):
        fields = ", ".join(field._template() for field in self.fields)
        if self.reducer is not None:
            return "{}({})".format(self.reducer, fields)
        return "({},)".format(fields)


################################################################################
# Helper Functions: Generator Factory
################################################################################

def _make_generator(expression, type_token, parent, nest=False):
    if type_token.is_array:
        return ArrayFieldGenerator(expression, type_token, parent)
    else:
        # there are no arrays directly under arrays
        loop = parent._loop_context
        if nest:
            assert parent.ros_type.is_array
            loop = loop.nest(parent)
            expression = "".join((parent.expression, "[#",
                                  str(loop.depth), "]"))
        if not type_token.is_primitive:
            return CompositeFieldGenerator(expression, type_token, parent,
                                           _loop_context=loop)
        else:
            return FieldGenerator(expression, type_token, parent,
                                  _loop_context=loop)


################################################################################
# Internal Structures: Statement
################################################################################

# This is what the template engine will see and use.
# That is why we need these dumb properties that basically do the same as
# `isinstance()`.
# Each statement can be version-stamped individually (`build_number`), allowing
# the construction of a field to span multiple non-sequential lines of code.

class _Statement(object):
    __slots__ = ("field", "build_number")

    def __init__(self, field):
        self.field = field # _LocalReference
        self.build_number = 0

    def available(self, build_number):
        return self.field.available(build_number)

    def build(self):
        assert False, "subclasses must implement this"

    @property
    def is_strategy(self):
        assert False, "subclasses must implement this"

    @property
    def is_assumption(self):
        assert False, "subclasses must implement this"

    def _enclosing_loops(self, statement):
        loops = []
        ctx = self.field.field._loop_context
        loops.extend(ctx.loops(var="i"))
        if loops:
            if statement.is_assignment:
                statement.field = statement.field.replace("#", "i")
                statement.expression = statement.expression.replace("#", "i")
            elif statement.is_assumption:
                for condition in statement.conditions:
                    condition.field = condition.field.replace("#", "i")
        loops.extend(self._loops_from_values("j"))
        for var, expr, excl in reversed(loops):
            statement = RangeLoop(expr, statement, excluding=excl, var=var)
        return statement

    def _loops_from_values(self, var):
        return ()


################################################################################
# Initialization Statements: Strategies
################################################################################

class _Strategy(_Statement):
    __slots__ = _Statement.__slots__

    NOOP = 0
    DEFAULT = 1
    RANDOM_W_CONSTRAINT = 2
    ENUM = 3
    CONSTANT = 4

    @property
    def is_strategy(self):
        return True

    @property
    def is_assumption(self):
        return False

    @property
    def level(self):
        assert False, "subclasses must implement this"

    @property
    def is_default(self):
        return False

    @property
    def is_noop(self):
        return False

    @property
    def is_random_number(self):
        return False

    @property
    def is_enum(self):
        return False

    @property
    def is_constant(self):
        return False

    @property
    def is_random(self):
        return True

    @property
    def is_drawn(self):
        return True

    @property
    def type_name(self):
        return self.field.type_name


class _NoopStrategy(_Strategy):
    __slots__ = _Strategy.__slots__

    @property
    def level(self):
        return self.NOOP

    @property
    def is_random(self):
        return False

    @property
    def is_drawn(self):
        return False

    @property
    def is_noop(self):
        return True

    def available(self, build_number):
        return True

    def build(self):
        return None


class _DefaultStrategy(_Strategy):
    __slots__ = _Strategy.__slots__

    @property
    def level(self):
        return self.DEFAULT

    @property
    def is_default(self):
        return True

    def build(self):
        field = self.field.field
        if field.ros_type.is_array:
            if field.ros_type.is_fixed_length:
                value = "[{}]".format(", ".join(
                    None for i in range(field.ros_type.length)))
            else:
                value = RandomArray(field.min_length, field.max_length,
                                    field.set_length)
        else:
            if field.ros_type.is_primitive:
                value = RandomValue(self.field.type_name)
            else:
                value = RandomValue(self.field.type_name, msg=field.expression)
        statement = Assignment(field.expression, value)
        return self._enclosing_loops(statement)

    def _template(self):
        if self.field.field.ros_type.is_array:
            array = self.field.field
            parts = ["strategies.lists(strategies.none(), min_size=",
                     str(array.min_length)]
            if array.ros_type.is_fixed_length:
                parts.append(", max_size=")
                parts.append(str(array.min_length))
            parts.append(")")
            return "".join(parts)
        else:
            return "ros_{}()".format(self.type_name)


class _NumberInterval(_Strategy):
    __slots__ = _Strategy.__slots__ + ("min_values", "max_values")

    def __init__(self, field):
        assert field.field.ros_type.is_number
        _Strategy.__init__(self, field)
        self.min_values = set()
        self.max_values = set()

    @property
    def level(self):
        return self.RANDOM_W_CONSTRAINT

    @property
    def is_random_number(self):
        return True

    def available(self, build_number):
        return (_Strategy.available(self, build_number)
                and all(v.available(build_number) for v in self.min_values)
                and all(v.available(build_number) for v in self.max_values))

    def build(self):
        args = {}
        if len(self.min_values) > 1:
            args["min_value"] = "max({})".format(
                ", ".join(str(v) for v in self.min_values))
        elif len(self.min_values) == 1:
            for low in self.min_values:
                args["min_value"] = str(low)
        if len(self.max_values) > 1:
            args["max_value"] = "min({})".format(
                ", ".join(str(v) for v in self.max_values))
        elif len(self.max_values) == 1:
            for high in self.max_values:
                args["max_value"] = str(high)
        value = RandomValue(self.field.type_name, **args)
        statement = Assignment(self.field.field.expression, value)
        return self._enclosing_loops(statement)

    def _loops_from_values(self, var):
        loops = []
        seq = 1
        prefix = var + str(seq) + "_"
        for value in self.min_values:
            vl = value.loops(var=prefix)
            if vl:
                loops.extend(vl)
                seq += 1
                prefix = var + str(seq) + "_"
        for value in self.max_values:
            vl = value.loops(var=prefix)
            if vl:
                loops.extend(vl)
                seq += 1
                prefix = var + str(seq) + "_"
        return loops

    def _template(self):
        assert len(self.min_values) > 0
        if len(self.min_values) > 1:
            low = "max({})".format(", ".join(str(v) for v in self.min_values))
        else:
            for low in self.min_values:
                break
            low = str(low)
        assert len(self.max_values) > 0
        if len(self.max_values) > 1:
            high = "min({})".format(", ".join(str(v) for v in self.max_values))
        else:
            for high in self.max_values:
                break
            high = str(high)
        return "ros_{}(min_value={}, max_value={})".format(
            self.field.type_name, low, high)


class _EqualTo(_Strategy):
    __slots__ = _Strategy.__slots__ + ("value",)

    def __init__(self, field, value):
        _Strategy.__init__(self, field)
        self.value = value

    def available(self, build_number):
        return (_Strategy.available(self, build_number)
                and self.value.available(build_number))

    def build(self):
        statement = Assignment(self.field.field.expression, str(self.value))
        return self._enclosing_loops(statement)

    def _loops_from_values(self, var):
        return self.value.loops(var=var)

    @property
    def level(self):
        return self.CONSTANT

    @property
    def is_constant(self):
        return True

    @property
    def is_random(self):
        return False

    @property
    def is_drawn(self):
        return False

    def _template(self):
        return str(self.value)


class _SampledFrom(_Strategy):
    __slots__ = _Strategy.__slots__ + ("values",)

    def __init__(self, field, values):
        _Strategy.__init__(self, field)
        self.values = list(values)

    def available(self, build_number):
        return (_Strategy.available(self, build_number)
                and all(value.available(build_number) for value in self.values))

    def build(self):
        if len(self.values) > 1:
            value = RandomSample(list(map(str, self.values)))
        else:
            value = str(self.values[0])
        statement = Assignment(self.field.field.expression, value)
        return self._enclosing_loops(statement)

    def _loops_from_values(self, var):
        loops = []
        seq = 1
        prefix = var + str(seq) + "_"
        for value in self.values:
            vl = value.loops(var=prefix)
            if vl:
                loops.extend(vl)
                seq += 1
                prefix = var + str(seq) + "_"
        return loops

    @property
    def level(self):
        return self.ENUM

    @property
    def is_enum(self):
        return True

    @property
    def is_random(self):
        return False

    def _template(self):
        if len(self.values) > 1:
            return "strategies.sampled_from(({},))".format(
                ", ".join(str(value) for value in self.values))
        else:
            return "strategies.just({})".format(self.values[0])


################################################################################
# Additional Statements: Assumptions
################################################################################

class _Assumption(_Statement):
    __slots__ = _Statement.__slots__ + ("value", "operator", "function")

    def __init__(self, field, value, operator, fun=None):
        _Statement.__init__(self, field)
        self.value = value
        self.operator = operator
        self.function = fun

    def available(self, build_number):
        return (_Statement.available(self, build_number)
                and self.value.available(build_number))

    def build(self):
        if self.function:
            expr = "{}({})".format(self.function, self.field.field.expression)
        else:
            expr = self.field.field.expression
        condition = FieldCondition(expr, self.operator, str(self.value))
        statement = Assumption([condition])
        return self._enclosing_loops(statement)

    def _loops_from_values(self, var):
        return self.value.loops(var=var)

    @property
    def is_strategy(self):
        return False

    @property
    def is_assumption(self):
        return True

    @property
    def aggregated(self):
        return False

    def _template(self):
        return "{} {} {}".format(str(self.field), self.operator,
                                 str(self.value))


class _Or(_Assumption):
    __slots__ = _Statement.__slots__ + ("assumptions",)

    def __init__(self, *assumptions):
        _Statement.__init__(self, assumptions[0].field)
        self.assumptions = assumptions

    def available(self, build_number):
        return all(a.available(build_number) for a in self.assumptions)

    def build(self):
        conditions = [FieldCondition(
                a.field.field.expression, a.operator, str(a.value))
                for a in self.assumptions]
        statement = Assumption(Disjunction(conditions))
        return self._enclosing_loops(statement)

    def _loops_from_values(self, var):
        loops = []
        seq = 1
        prefix = var + str(seq) + "_"
        for assumption in self.assumptions:
            vl = assumption.value.loops(var=prefix)
            if vl:
                loops.extend(vl)
                seq += 1
                prefix = var + str(seq) + "_"
        return loops


################################################################################
# Internal Structures: Value Wrappers
################################################################################

# This is here just to make polymorphism easier/available.
# Otherwise we would have to `isinstance(value, _LocalReference)` everywhere,
# and possibly even in the template engine which is not a good idea.

class _ValueWrapper(object):
    __slots__ = ()

    @property
    def is_literal(self):
        assert False, "subclasses must implement this"

    @property
    def is_local_reference(self):
        assert False, "subclasses must implement this"

    @property
    def is_arg_reference(self):
        assert False, "subclasses must implement this"

    def available(self, build_number):
        assert False, "subclasses must implement this"

    def loops(self, var="i"):
        return ()


class _LiteralWrapper(_ValueWrapper):
    __slots__ = _ValueWrapper.__slots__ + ("value",)

    def __init__(self, value):
        self.value = value

    @property
    def is_literal(self):
        return True

    @property
    def is_local_reference(self):
        return False

    @property
    def is_arg_reference(self):
        return False

    def available(self, build_number):
        return True

    def __eq__(self, other):
        if not isinstance(other, _LiteralWrapper):
            return False
        return self.value == other.value

    def __hash__(self):
        return hash(self.value)

    def __str__(self):
        s = str(self.value)
        if isinstance(self.value, basestring):
            if s.startswith(('"', "'")):
                return s
            return '"{}"'.format(s)
        return s


################################################################################
# Internal Structures: Local Field References
################################################################################

class _LocalReference(_ValueWrapper):
    __slots__ = _ValueWrapper.__slots__ + ("field", "required_state")

    def __init__(self, generator, required_state):
        generator.reference_count += 1
        self.field = generator
        self.required_state = required_state

    @property
    def is_literal(self):
        return False

    @property
    def is_local_reference(self):
        return True

    @property
    def is_arg_reference(self):
        return False

    @property
    def type_name(self):
        return self.field.ros_type.type_name

    @property
    def is_array(self):
        return self.field.ros_type.is_array

    def available(self, build_number):
        return self.field.state(build_number) >= self.required_state

    def loops(self, var="i"):
        return self.field._loop_context.loops(var=var)

    def __eq__(self, other):
        if not isinstance(other, _LocalReference):
            return False
        return (self.field == other.field
                and self.required_state == other.required_state)

    def __hash__(self):
        return 31 * hash(self.field) + hash(self.required_state)

    def __str__(self):
        return self.field.expression


################################################################################
# Internal Structures: Function Argument References
################################################################################

class _ArgReference(_ValueWrapper):
    __slots__ = _ValueWrapper.__slots__ + ("arg_name", "selector")

    def __init__(self, arg_name, selector):
        self.arg_name = arg_name
        self.selector = selector

    @property
    def is_literal(self):
        return False

    @property
    def is_local_reference(self):
        return False

    @property
    def is_arg_reference(self):
        return True

    def available(self, build_number):
        return True

    def loops(self, var="i"):
        return ()

    def __eq__(self, other):
        if not isinstance(other, _ArgReference):
            return False
        return (self.arg_name == other.arg_name
                and self.selector == other.selector)

    def __hash__(self):
        return 31 * hash(self.arg_name) + hash(self.selector)

    def __str__(self):
        return "".join((self.arg_name, ".", self.selector.expression))


################################################################################
# Internal Structures: Loop Context
################################################################################

class _LoopContext(object):
    __slots__ = ("arrays",)

    def __init__(self, arrays):
        self.arrays = arrays

    @property
    def depth(self):
        return len(self.arrays)

    @property
    def variable(self):
        return "i" + str(len(self.arrays) + 1)

    def nest(self, array):
        return _LoopContext(self.arrays + (array,))

    def loops(self, var="i"):
        loops = []
        for array in self.arrays:
            expr = array.expression.replace("#", var)
            loop_var = var + str(len(loops) + 1)
            loops.append((loop_var, expr, list(array.fields.keys())))
        return loops
