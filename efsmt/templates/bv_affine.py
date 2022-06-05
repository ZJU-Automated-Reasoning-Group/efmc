# coding: utf-8
import z3
from typing import List

from .abstract_template import TemplateType, Template
from ..sts import TransitionSystem

"""
Affine relation domain over bit-vectors

There are several different variants
Some references
- Matt elder et al., Abstract domains of affine relations, TOPLAS'14
- Olm and Seidl, Precise interprocedural analysis through linear algebra, POPL'04
- King and Sondergaard,
     Inferring congruence equations using SAT, CAV'08
     Automatic abstraction for congruences, VMCAI'10
"""


class BitVecAffineTemplate(Template):

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
