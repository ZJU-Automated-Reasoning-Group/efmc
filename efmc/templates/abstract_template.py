# coding: utf-8
from enum import Enum
import z3


class TemplateType(Enum):
    POLYHEDRON = 0
    INTERVAL = 1
    ZONE = 2
    OCTAGON = 3
    DISJUNCTIVE_POLYHEDRON = 4
    DISJUNCTIVE_INTERVAL = 5
    DISJUNCTIVE_ZONE = 6
    DISJUNCTIVE_OCTAGON = 7
    BV_INTERVAL = 8
    BV_AFFINE_RELATION = 9
    ARRAY = 10
    STRING = 11
    FLOAT = 12


class Template(object):
    """
    Abstract interface for template-based verification
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
