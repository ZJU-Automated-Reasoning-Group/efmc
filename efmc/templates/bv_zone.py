# coding: utf-8
import z3
from typing import List
from .abstract_template import TemplateType, Template
from ..sts import TransitionSystem


class BitVecZoneTemplate(Template):

    def __init__(self, sts: TransitionSystem):
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
