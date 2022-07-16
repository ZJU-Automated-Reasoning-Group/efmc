# coding: utf-8
from enum import Enum
import z3


class TemplateType(Enum):
    """Template type"""
    INTERVAL = 0
    ZONE = 1
    OCTAGON = 2
    AFFINE = 3
    POLYHEDRON = 4
    DISJUNCTIVE_INTERVAL = 5
    DISJUNCTIVE_ZONE = 6
    DISJUNCTIVE_OCTAGON = 7
    DISJUNCTIVE_AFFINE = 8
    DISJUNCTIVE_POLYHEDRON = 9
    ARRAY = 10
    STRING = 11
    FLOAT = 12
    BV_INTERVAL = 13
    BV_ZONE = 14
    BV_OCTAGON = 15
    BV_AFFINE = 16
    BV_POLYHEDRON = 17
    BV_DISJUNCTIVE_INTERVAL = 18
    BV_DISJUNCTIVE_ZONE = 19
    BV_DISJUNCTIVE_OCTAGON = 20
    BV_DISJUNCTIVE_AFFINE = 21
    BV_DISJUNCTIVE_POLYHEDRON = 22


class Template(object):
    """Abstract interface for template-based verification
    """

    def add_template_vars(self):
        raise NotImplementedError

    def add_template_cnts(self):
        raise NotImplementedError

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables: bool):
        """
        Build an invariant from a model, i.e., fixing the values of the template vars
        :param model the model used for building expr
        :param use_prime_variables deciding using x, y or x!, y!
        """
        raise NotImplementedError
