# coding: utf-8
# from typing import List
import logging
import z3
from ..sts import TransitionSystem
from .abstract_template import TemplateType, Template


logger = logging.getLogger(__name__)


class ArrayTemplate(Template):
    """
    Currently, we focus on ALIA.
    TODO: a major challenge is to infer "quantified invariants"
    E.g., https://www.cs.upc.edu/~albert/papers/vmcai2013.pdf
    """

    def __init__(self, system: TransitionSystem):
        self.template_type = TemplateType.ARRAY
        self.sts = system
        # TODO: we should be "directly" pass system to IntervalTemplate
        # because it only deals with int/real?

        self.numeric_template = None

    def build_numeric_domain(self):
        return

    def add_template_vars(self):
        self.numeric_template.add_teplate_vars()

    def add_template_cnts(self):
        raise NotImplementedError

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables: bool):
        raise NotImplementedError


class UFTemplate(Template):
    """
    Currently, we focus on UFLIA
    """

    def __init__(self, system: TransitionSystem):
        self.template_type = TemplateType.ARRAY
        self.sts = system
        # TODO: we should be "directly" pass system to IntervalTemplate
        # because it only deals with int/real?

        self.numeric_template = None

    def build_numeric_domain(self):
        return

    def add_template_vars(self):
        self.numeric_template.add_teplate_vars()

    def add_template_cnts(self):
        raise NotImplementedError

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables: bool):
        raise NotImplementedError
