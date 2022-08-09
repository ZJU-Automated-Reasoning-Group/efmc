"""Affine domain over integer or real variables
"""
import logging
import z3
from efmc.templates.abstract_template import TemplateType, Template
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


class AffineTemplate(Template):
    """
    Affine relation (linear equality) analysis
    """

    def __init__(self, system: TransitionSystem):
        self.template_type = TemplateType.OCTAGON

        self.use_real = True
        self.sts = system

    def add_template_vars(self):
        raise NotImplementedError

    def add_template_cnts(self):
        raise NotImplementedError

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables: bool):
        raise NotImplementedError
