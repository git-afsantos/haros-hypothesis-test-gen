# -*- coding: utf-8 -*-

# SPDX-License-Identifier: MIT
# Copyright © 2021 André Santos

###############################################################################
# Imports
###############################################################################

from __future__ import unicode_literals
from builtins import str

from hpl.ast import HplVacuousTruth
from hpl.grammar import PREDICATE_GRAMMAR
from hpl.parser import PropertyTransformer
from lark import Lark
from lark.exceptions import UnexpectedCharacters, UnexpectedToken

###############################################################################
# Grammar
###############################################################################

SCHEMA_GRAMMAR = r'''
schema: _list_of_statements?

_list_of_statements: [_list_of_statements] _statement

_statement: publish_statement
          | forbid_statement

publish_statement: timestamp "publish" event

forbid_statement: "forbid" event

event: ros_name predicate?

timestamp: "+" INT ".." [INT] ":"
''' + PREDICATE_GRAMMAR


###############################################################################
# Parser
###############################################################################

class SchemaParseError(Exception):
    @classmethod
    def upper_bound(cls, ub, lb):
        return cls('upper bound <= lower bound: +{}..{}'.format(lb, ub))


class SchemaTransformer(PropertyTransformer):
    def schema(self, children):
        return list(children)

    def publish_statement(self, children):
        n = len(children)
        assert n == 2, n
        return ('publish', children[0], children[1])

    def forbid_statement(self, children):
        n = len(children)
        assert n == 1, n
        return ('forbid', children[0])

    def event(self, children):
        n = len(children)
        assert n == 1 or n == 2, n
        ros_name = children[0]
        phi = HplVacuousTruth() if n == 1 else children[1]
        return (ros_name, phi)

    def timestamp(self, children):
        n = len(children)
        assert n == 1 or n == 2, n
        lb = int(children[0])
        if n == 1:
            ub = None
        else:
            ub = int(children[1])
            if ub <= lb:
                raise SchemaParseError.upper_bound(ub, lb)
        return (lb, ub)


def parse(text, debug=False):
    lark = Lark(SCHEMA_GRAMMAR, parser='lalr', start='schema',
                transformer=SchemaTransformer(), debug=debug)
    try:
        return lark.parse(text)
    except (UnexpectedToken, UnexpectedCharacters, SyntaxError) as e:
        raise SchemaParseError(str(e))
