"""Polyhedral template over integer or real variables
"""
# from typing import List
import logging
import z3
from efmc.engines.ef.templates.abstract_template import TemplateType, Template
from efmc.sts import TransitionSystem


logger = logging.getLogger(__name__)


class PolyTemplate(Template):

    def __init__(self, sts: TransitionSystem):

        self.template_type = TemplateType.POLYHEDRON

        # TODO: perhaps we should block sts that is does not use reals?
        self.use_real = True

        self.sts = sts
        self.arity = len(self.sts.variables)

        self.template_vars = []  # vector of vector
        self.template_index = 0  # number of templates

        self.num_templates = 1  # this is for polyhedral

        self.add_template_vars()  # init self.template_vars

        # pre compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()  # init the above constraints

        # print(self.template_cnt_init_and_post)
        # print(self.template_cnt_trans)

    def add_template_vars(self):
        """
        Initialize self.template_vars

        E.g., assume that self.sts.variables are [x, y]. We will add two templates
            p1_0 + x*p1_1 + y*p2_2  >= 0
            p2_0 + x*p2_1 + y*p2_2  >= 0

        After this function, self.template_vars will be:
        [[p1_0, p1_1, p1_2], [p2_0, p2_1, p2_2]]
        """
        for _ in range(self.num_templates):
            self.template_index += 1
            if self.use_real:
                tvars = [z3.Real("p%d_%d" % (self.template_index, 0))]
            else:
                tvars = [z3.Int("p%d_%d" % (self.template_index, 0))]

            for i in range(1, self.arity + 1):
                if self.use_real:
                    tvars.append(z3.Real("p%d_%d" % (self.template_index, i)))
                else:
                    tvars.append(z3.Int("p%d_%d" % (self.template_index, i)))

            self.template_vars.append(tvars)
        # print(self.template_vars)

    def add_template_cnts(self):
        """
        For initializing self.template_cnt_init_and_post and self.template_cnt_trans
        """
        cnts_init_post = []  # For sts.variables
        cnts_trans = []  # For sts.prime_variables
        for i in range(self.template_index):  # num. of templates
            term_init_post = self.template_vars[i][0]
            term_trans = self.template_vars[i][0]

            for j in range(1, self.arity + 1):
                # For sts.variables
                term_init_post = term_init_post + self.sts.variables[j - 1] * self.template_vars[i][j]

                # For sts.prime_variables
                term_trans = term_trans + self.sts.prime_variables[j - 1] * self.template_vars[i][j]

            cnts_init_post.append(term_init_post >= 0)
            cnts_trans.append(term_trans >= 0)

        if len(cnts_init_post) > 1:
            self.template_cnt_init_and_post = z3.And(cnts_init_post)
        else:
            self.template_cnt_init_and_post = cnts_init_post[0]

        if len(cnts_init_post) > 1:
            self.template_cnt_trans = z3.And(cnts_trans)
        else:
            self.template_cnt_trans = cnts_trans[0]

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False) -> z3.ExprRef:
        """
        Build an invariant from a model, i.e., fixing the values of the template vars
        :param model the model used for building expr
        :param use_prime_variables deciding using x, y or x!, y!
        """
        cnts = []
        for i in range(self.template_index):  # num. of templates
            term = model[self.template_vars[i][0]]
            for j in range(1, self.arity + 1):
                tvar = self.template_vars[i][j]
                # model[tvar] is the value of tvar in the model
                if use_prime_variables:
                    term = term + self.sts.prime_variables[j - 1] * model[tvar]
                else:
                    term = term + self.sts.variables[j - 1] * model[tvar]
            cnts.append(term >= 0)
        if len(cnts) > 1:
            return z3.And(cnts)
        else:
            return cnts[0]


class DisjunctivePolyTemplate(Template):
    """
    Polyhedral domain
    """

    def __init__(self, sts: TransitionSystem):
        # TODO: perhaps we should block sts that is does not use reals?
        raise NotImplementedError

    def add_template_vars(self):
        raise NotImplementedError

    def add_template_cnts(self):
        raise NotImplementedError

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables: bool):
        raise NotImplementedError
