"""Bit-vector Zone Domain
"""
import itertools

import z3

from efmc.sts import TransitionSystem
from efmc.templates.abstract_template import TemplateType, Template
from efmc.templates.bv_utils import Signedness
from efmc.utils import get_variables


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
        # follow interval, but use self.zones
        for i in range(len(self.zones)):
            term = self.zones[i]
            term_vars = get_variables(term)
            term_name = "{}{}".format(term_vars[0], term_vars[1])
            self.template_index += 1
            tvars = [z3.BitVec("b{}l".format(term_name), term.size()),
                     z3.BitVec("b{}u".format(term_name), term.size())]
            self.template_vars.append(tvars)
        # raise NotImplementedError

    def get_additional_cnts_for_template_vars(self):
        return z3.BoolVal(True)

    def add_template_cnts(self):
        # TODO: test correctness
        cnts = []
        cnts_prime = []
        for i in range(len(self.zones)):
            term = self.zones[i]  # e.g., x - y
            term_prime = self.prime_zones[i]  # e.g., x' - y'
            template_vars_for_term = self.template_vars[i]
            term_l = template_vars_for_term[0]  # lower bound of the term
            term_u = template_vars_for_term[1]  # upper bound of the term

            if self.signedness == Signedness.UNSIGNED:
                cnts.append(z3.And(z3.ULE(term_l, term), z3.UGE(term_u, term)))
                cnts_prime.append(z3.And(z3.ULE(term_l, term_prime),
                                         z3.UGE(term_u, term_prime)))
            else:
                cnts.append(z3.And(term_l <= term, term_u >= term))
                cnts_prime.append(z3.And(term_l <= term_prime,
                                         term_u >= term_prime))

        self.template_cnt_init_and_post = z3.And(cnts)
        self.template_cnt_trans = z3.And(cnts_prime)
        # raise NotImplementedError

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """
        Build the inductive invariant corresponding to a model, which is obtained by
         solving the exists-forall formula encoding the verification condition
        """
        cnts = []
        for i in range(len(self.zones)):
            if use_prime_variables:
                term = self.prime_zones[i]
            else:
                term = self.zones[i]
            template_vars_for_term = self.template_vars[i]
            term_l = template_vars_for_term[0]  # lower bound of the term
            term_u = template_vars_for_term[1]  # upper bound of the term

            if self.signedness == Signedness.UNSIGNED:
                cnts.append(z3.And(model[term_l] <= term, model[term_u] >= term))
            else:
                cnts.append(z3.And(z3.ULE(model[term_l], term), z3.UGE(model[term_u], term)))

        return z3.And(cnts)


class DisjunctiveBitVecZoneTemplate(Template):

    def __init__(self, sts: TransitionSystem):
        self.template_type = TemplateType.BV_DISJUNCTIVE_ZONE

        # TODO: infer the signedness of variables? (or design a domain that is signedness-irrelevant
        self.signedness = Signedness.UNSIGNED

        self.sts = sts
        self.arity = len(self.sts.variables)

        self.template_vars = []  # vector of vector
        self.template_index = 0  # number of templates

        self.num_of_disjuncts = 2

        self.add_template_vars()

        # pre compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()

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
