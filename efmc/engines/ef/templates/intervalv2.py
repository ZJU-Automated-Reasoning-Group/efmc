"""Interval template over integer or real variables  (Version 2)

   It seems that the encoding in this version is not complete
"""
import logging

import z3

from efmc.sts import TransitionSystem
# from typing import List
from efmc.engines.ef.templates.abstract_template import TemplateType, Template
from efmc.utils import big_and

logger = logging.getLogger(__name__)



class IntervalTemplateV2(Template):
    """
    Interval domain (it seems that this one does not work)
    FIXME: The current IntervalTemplate introduces non-linear cnts, which are not elegant.
      However, due to the problem of infinity (?), we cannot use the following kind of templates
      a <= x <= b,  c <= y <= d (this seems to restrict the values of a, b, c, d)
      The above template leads to incompleteness (?)
      But, can we use a < x < b,  c < y < d (e.g., for integers?)
    """

    def __init__(self, sts: TransitionSystem, **kwargs):

        self.template_type = TemplateType.INTERVAL

        if sts.has_real:
            self.use_real = True
        else:
            self.use_real = False

        self.sts = sts
        self.arity = len(self.sts.variables)

        self.template_vars = []  # vector of vector
        self.template_index = 0  # number of templates

        self.add_template_vars()

        # pre_compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()

    def add_template_vars(self):
        """
        Add several groups of template vars
        Assume that self.sts.inv_vars are [x, y], we will add two templates
            l_x <= x <= u_x
            l_y <= y <= u_y
        After this function, self.template_vars will be:
        [[l_x, u_x], [l_y, u_y]]
        """
        for var in self.sts.variables:
            if self.use_real:
                tvars = [z3.Real("l_{}".format(str(var))), z3.Real("u_{}".format(str(var)))]
            else:
                tvars = [z3.Int("l_{}".format(str(var))), z3.Int("u_{}".format(str(var)))]
            self.template_vars.append(tvars)
            self.template_index += 1

    def get_additional_cnts_for_template_vars(self):
        """This implementation does not need additional ones?"""
        return z3.BoolVal(True)

    def add_template_cnts(self):
        """Add cnts for init and post assertions (a trick)"""
        cnts = []
        cnts_prime = []
        for i in range(self.arity):
            var = self.sts.variables[i]
            var_prime = self.sts.prime_variables[i]
            var_l = self.template_vars[i][0]  # lower bound
            var_u = self.template_vars[i][1]  # upper bound

            cnts.append(z3.And(var_l <= var, var_u >= var))
            cnts_prime.append(z3.And(var_l <= var_prime, var_u >= var_prime))

        self.template_cnt_init_and_post = big_and(cnts)
        self.template_cnt_trans = big_and(cnts_prime)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """Build an invariant from a model (fixing the values of the template vars)"""
        cnts = []
        for i in range(self.arity):
            if use_prime_variables:
                var = self.sts.prime_variables[i]
            else:
                var = self.sts.variables[i]
            tvar_l = self.template_vars[i][0]
            tvar_u = self.template_vars[i][1]
            cnts.append(z3.And(model[tvar_l] <= var, model[tvar_u] >= var))
        return big_and(cnts)

    def add_template_cnts_for_ranking_function(self):
        raise NotImplementedError

    def build_ranking_function_expr(self):
        raise NotImplementedError


class DisjunctiveIntervalTemplateV2:

    def __init__(self):
        raise NotImplementedError


