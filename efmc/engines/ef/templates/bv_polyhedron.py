"""Template polyhedral domain over bit-vectors
"""
import z3
# from typing import List

from efmc.engines.ef.templates.abstract_template import TemplateType, Template
from efmc.sts import TransitionSystem


class BitVecPolyhedronTemplate(Template):
    """
    """

    def __init__(self, sts: TransitionSystem):
        self.template_type = TemplateType.BV_POLYHEDRON

        self.sts = sts

    def add_template_vars(self):
        """
        Add several groups of template vars
        """
        raise NotImplementedError

    def get_additional_cnts_for_template_vars(self):
        """
        This implementation does not need additional ones?
        """
        raise NotImplementedError

    def add_template_cnts(self):
        """
        Add cnts for init and post assertions (a trick)
        """
        raise NotImplementedError

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """
        Build an invariant from a model (fixing the values of the template vars)
        """
        raise NotImplementedError


class DisjunctiveBitVecPolyhedronTemplate(Template):
    """
    TODO: There are several different variants. Some references
    """

    def __init__(self, sts: TransitionSystem):
        self.template_type = TemplateType.BV_DISJUNCTIVE_POLYHEDRON

        self.sts = sts

    def add_template_vars(self):
        """
        Add several groups of template vars
        """
        raise NotImplementedError

    def get_additional_cnts_for_template_vars(self):
        """
        This implementation does not need additional ones?
        """
        raise NotImplementedError

    def add_template_cnts(self):
        """
        Add cnts for init and post assertions (a trick)
        """
        raise NotImplementedError

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """
        Build an invariant from a model (fixing the values of the template vars)
        """
        raise NotImplementedError
