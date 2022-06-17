# coding: utf-8
# from typing import List
import logging
import itertools
import z3
from .abstract_template import TemplateType, Template
from ..sts import TransitionSystem
from ..utils import get_variables


logger = logging.getLogger(__name__)


class ZoneTemplate(Template):
    """
    Zone domain

    FIXME: maybe has flaws (if the solution for interval works, maybe borrow that one)

    """

    def __init__(self, sts: TransitionSystem):

        self.template_type = TemplateType.ZONE

        self.use_real = True

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
            if self.use_real:
                tvars = [z3.Real("i{}0".format(term_name)), z3.Real("i{}1".format(term_name)),
                         z3.Real("i{}2".format(term_name)), z3.Real("i{}3".format(term_name))]
            else:
                tvars = [z3.Int("i{}0".format(term_name)), z3.Int("i{}1".format(term_name)),
                         z3.Int("i{}2".format(term_name)), z3.Int("i{}3".format(term_name))]
            self.template_vars.append(tvars)
        # print(self.template_vars)

    def get_additional_cnts_for_template_vars(self):
        """
        Is this correct?
        """
        cnts = []
        for tvars in self.template_vars:
            i0, i1, i2, i3 = tvars[0], tvars[1], tvars[2], tvars[3]
            # the second means "no lower bound"?
            cnts.append(z3.Or(i1 == 1, z3.And(i1 == 0, i0 == 0)))
            # the second means "no upper bound"?
            cnts.append(z3.Or(i3 == -1, z3.And(i3 == 0, i2 == 0)))
        return z3.And(cnts)

    def add_template_cnts(self):
        cnts_init_post = []  # For sts.variables
        cnts_trans = []  # For sts.prime_variables

        for i in range(len(self.zones)):
            term = self.zones[i]
            prime_term = self.prime_zones[i]
            template_vars_for_var = self.template_vars[i]

            i0, i1 = template_vars_for_var[0], template_vars_for_var[1]
            i2, i3 = template_vars_for_var[2], template_vars_for_var[3]

            cnts_init_post.append(i0 + term * i1 >= 0)
            cnts_init_post.append(i2 + term * i3 >= 0)

            cnts_trans.append(i0 + prime_term * i1 >= 0)
            cnts_trans.append(i2 + prime_term * i3 >= 0)

        self.template_cnt_init_and_post = z3.And(cnts_init_post)
        self.template_cnt_trans = z3.And(cnts_trans)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """
        TODO: the following is for interval
        """
        cnts = []

        for i in range(len(self.zones)):
            if use_prime_variables:
                term = self.prime_zones[i]
            else:
                term = self.zones[i]

            template_vars_for_term = self.template_vars[i]  # this does not work!
            i0, i1 = template_vars_for_term[0], template_vars_for_term[1]
            i2, i3 = template_vars_for_term[2], template_vars_for_term[3]

            if model[i1].as_long() != 0:
                cnts.append(model[i0] + term * model[i1] >= 0)
            if model[i3].as_long() != 0:
                cnts.append(model[i2] + term * model[i3] >= 0)

        return z3.And(cnts)