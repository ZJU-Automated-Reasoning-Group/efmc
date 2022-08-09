"""Bit-vector Zone Domain
"""
import itertools

import z3
from efmc.templates.abstract_template import TemplateType, Template
from efmc.sts import TransitionSystem
from efmc.templates.bv_utils import Signedness


class BitVecZoneTemplate(Template):

    def __init__(self, sts: TransitionSystem):

        self.template_type = TemplateType.BV_ZONE

        # TODO: infer the signedness of variables? (or design a domain that is signedness-irrelevant
        self.signedness = Signedness.UNSIGNED

        self.sts = sts
        self.arity = len(self.sts.variables)
        assert (self.arity >= 2)
        assert (len(self.sts.prime_variables) >= 2)

        self.zones = []
        for x, y in list(itertools.combinations(self.sts.variables, 2)):
            self.zones.append(x - y)
        self.prime_zones = []
        for px, py in list(itertools.combinations(self.sts.prime_variables, 2)):
            self.prime_zones.append(px - py)

        self.template_vars = []  # vector of vector
        self.template_index = 0  # number of templates

        self.add_template_vars()

        # pre compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()

    def add_template_vars(self):
        raise NotImplementedError

    def get_additional_cnts_for_template_vars(self):
        raise NotImplementedError

    def add_template_cnts(self):
        raise NotImplementedError

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        raise NotImplementedError


class DisjunctiveBitVecZoneTemplate(Template):

    def __init__(self, sts: TransitionSystem):
        self.template_type = TemplateType.BV_DISJUNCTIVE_ZONE

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
