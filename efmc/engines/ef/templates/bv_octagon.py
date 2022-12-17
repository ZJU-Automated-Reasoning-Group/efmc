"""Octagon template over bit-vector variables
"""
import itertools
import z3
from efmc.engines.ef.templates.abstract_template import Template, TemplateType
from efmc.engines.ef.templates.bv_utils import Signedness
from efmc.sts import TransitionSystem
from efmc.utils import get_variables, big_and


class BitVecOctagonTemplate(Template):

    def __init__(self, sts: TransitionSystem):
        self.sts = sts
        self.template_type = TemplateType.BV_OCTAGON
        # TODO: infer the signedness of variables? (or design a domain that is signedness-irrelevant
        self.signedness = Signedness.UNSIGNED
        # self.obj_no_overflow = False  # for controlling the behavior of x - y, x + y
        # self.obj_no_underflow = False

        self.sts = sts
        self.arity = len(self.sts.variables)
        assert (self.arity >= 2)
        assert (len(self.sts.prime_variables) >= 2)

        self.octagons = []
        for x, y in list(itertools.combinations(self.sts.variables, 2)):
            self.octagons.append(x - y)
            self.octagons.append(x + y)

        self.prime_octagons = []
        for px, py in list(itertools.combinations(self.sts.prime_variables, 2)):
            self.prime_octagons.append(px - py)
            self.prime_octagons.append(px + py)

        self.template_vars_for_vars = []  # aux variables for for x, y, z, ...
        self.template_vars_for_terms = []  # aux variables for x - y, x + y, x - z, ...
        self.template_index = 0  # number of templates

        # create template variables, e.g., if we care about the interval of x,
        # then the template cnts are a <= x <= b, where a and b are template variables
        self.add_template_vars()

        # pre_compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()

    def add_template_vars(self):
        """
        Add several groups of template vars
        """

        for var in self.sts.variables:
            tvars = [z3.BitVec("{}_l".format(str(var)), var.sort().size()),
                     z3.BitVec("{}_u".format(str(var)), var.sort().size())]
            self.template_vars_for_vars.append(tvars)

        # follow interval, but use self.octagon
        for i in range(len(self.octagons)):
            term = self.octagons[i]
            term_vars = get_variables(term)
            term_name = "{}{}".format(term_vars[0], term_vars[1])
            self.template_index += 1
            tvars = [z3.BitVec("{}_l".format(term_name), term.size()),
                     z3.BitVec("{}_u".format(term_name), term.size())]
            self.template_vars_for_terms.append(tvars)
        # raise NotImplementedError

    def get_additional_cnts_for_template_vars(self):
        """
        This implementation does not need additional ones?
        """
        return z3.BoolVal(True)

    def add_template_cnts(self):
        """
        Add cnts for init and post assertions (a trick)
        """
        cnts = []
        cnts_prime = []

        # Add constraints for x, y, z, ...
        for i in range(self.arity):
            var = self.sts.variables[i]
            var_prime = self.sts.prime_variables[i]
            var_l = self.template_vars_for_vars[i][0]  # lower bound
            var_u = self.template_vars_for_vars[i][1]  # upper bound
            if self.signedness == Signedness.UNSIGNED:
                cnts.append(z3.And(z3.UGE(var, var_l), z3.ULE(var, var_u)))
                cnts_prime.append(z3.And(z3.UGE(var_prime, var_l), z3.ULE(var_prime, var_u)))
            else:
                cnts.append(z3.And(var >= var_l, var <= var_u))
                cnts_prime.append(z3.And(var_prime >= var_l, var_prime <= var_u))

        # Add constraints for x - y, x + y, x - z, ...
        for i in range(len(self.octagons)):
            term = self.octagons[i]  # e.g., x - y
            term_prime = self.prime_octagons[i]  # e.g., x' - y'
            template_vars_for_term = self.template_vars_for_terms[i]
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

        self.template_cnt_init_and_post = big_and(cnts)
        self.template_cnt_trans = big_and(cnts_prime)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """
        Build an invariant from a model (fixing the values of the template vars)
        """
        cnts = []

        # For building formulas in the forms of a <= x < = b, c <= y < = d, ...
        for i in range(self.arity):
            if use_prime_variables:
                var = self.sts.prime_variables[i]
            else:
                var = self.sts.variables[i]
            tvar_l = self.template_vars_for_vars[i][0]
            tvar_u = self.template_vars_for_vars[i][1]
            if self.signedness == Signedness.UNSIGNED:
                cnts.append(z3.And(z3.UGE(var, model[tvar_l]), z3.ULE(var, model[tvar_u])))
            else:
                cnts.append(z3.And(var >= model[tvar_l], var <= model[tvar_u]))

        # For building formulas in the forms of a <= x - y <= b, c <= x + y <= d,...
        for i in range(len(self.octagons)):
            if use_prime_variables:
                term = self.prime_octagons[i]
            else:
                term = self.octagons[i]
            template_vars_for_term = self.template_vars_for_terms[i]
            term_l = template_vars_for_term[0]  # lower bound of the term
            term_u = template_vars_for_term[1]  # upper bound of the term

            if self.signedness == Signedness.UNSIGNED:
                cnts.append(z3.And(model[term_l] <= term, model[term_u] >= term))
            else:
                cnts.append(z3.And(z3.ULE(model[term_l], term), z3.UGE(model[term_u], term)))

        return z3.And(cnts)


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
