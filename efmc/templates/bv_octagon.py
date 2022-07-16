"""Octagon template over bit-vector variables
"""
import z3
from .abstract_template import Template, TemplateType
from ..sts import TransitionSystem


class BitVecOctagonTemplate(Template):

    def __init__(self, sts: TransitionSystem):
        self.sts = sts
        self.template_type = TemplateType.BV_OCTAGON

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


class DisjunctiveBitVecOctagonTemplate(Template):

    def __init__(self, sts: TransitionSystem):
        self.sts = sts
        self.template_type = TemplateType.BV_DISJUNCTIVE_OCTAGON

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