"""Interval template over integer or real variables  (Version 3)

"""
import logging

from efmc.engines.ef.templates.abstract_template import *
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


class IntervalTemplateV3(Template):
    """
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
        Assume that self.sts.inv_vars are [x, y], we will add the following templates
            a1 <= x <= a2  OR  a3 <= x  OR  x <= a4
            b1 <= y <= b2  OR  b3 <= y  OR  y <= b4
        After this function, self.template_vars will be:
        [[], []]
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

            cnts.append(z3.And(var_l < var, var_u > var))
            cnts_prime.append(z3.And(var_l < var_prime, var_u > var_prime))

        self.template_cnt_init_and_post = z3.And(cnts)
        self.template_cnt_trans = z3.And(cnts_prime)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """Build an invariant from a model (fixing the values of the template vars)"""
        raise NotImplementedError

    def add_template_cnts_for_ranking_function(self):
        raise NotImplementedError

    def build_ranking_function_expr(self):
        raise NotImplementedError


class DisjunctiveIntervalTemplateV3:

    def __init__(self):
        raise NotImplementedError
