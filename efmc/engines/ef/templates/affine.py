"""Affine domain over integer or real variables
# FIXME: it seems that this file is not implemented yet
"""

import logging
from efmc.engines.ef.templates.abstract_template import *
from efmc.sts import TransitionSystem
from efmc.utils import big_and, big_or

logger = logging.getLogger(__name__)


class AffineTemplate(Template):
    """
    Affine relation (linear equality) analysis
    """

    def __init__(self, system: TransitionSystem, **kwargs):
        self.template_type = TemplateType.AFFINE

        # self.use_real = True
        if system.has_real:
            self.use_real = True
        else:
            self.use_real = False
        self.sts = system

        self.arity = len(self.sts.variables)

        self.template_vars = []  # vector of vector
        self.template_index = 0  # number of templates

        #  number of linear inequalities (NOTE: interval, zone, and octagon domains do not need this)
        #  thus, the following field is polyhedron-specific
        self.num_templates = 1

        self.add_template_vars()  # init self.template_vars

        # pre_compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()  # init the above constraints

        # print(self.template_cnt_init_and_post)
        # print(self.template_cnt_trans)

    def add_template_vars(self):
        """
        Initialize self.template_vars

        E.g., assume that self.sts.variables are [x, y]. We will add two templates
            p1_0 + x*p1_1 + y*p1_2  == 0
                     AND
            p2_0 + x*p2_1 + y*p2_2  == 0

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

            cnts_init_post.append(term_init_post == 0)
            cnts_trans.append(term_trans == 0)

        self.template_cnt_init_and_post = big_and(cnts_init_post)
        self.template_cnt_trans = big_and(cnts_trans)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables: bool):
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
            cnts.append(term == 0)

        return big_and(cnts)


class DisjunctiveAffineTemplate(Template):
    """
    Affine relation (linear equality) analysis
    """

    def __init__(self, system: TransitionSystem, **kwargs):
        self.template_type = TemplateType.DISJUNCTIVE_AFFINE

        # self.use_real = True
        if system.has_real:
            self.use_real = True
        else:
            self.use_real = False

        #  number of linear inequalities (NOTE: interval, zone, and octagon domains do not need this)
        #  thus, the following field is polyhedron/affine-specific
        self.num_templates = 1  # (a1 AND a2 ..)  NOTE: now use for now. We always use 1.

        self.num_disjunctions = kwargs.get("num_disjunctions", 2)

        self.sts = system
        self.arity = len(self.sts.variables)

        self.template_vars = []  # vector of vector
        self.template_index = 0  # number of templates

        self.add_template_vars()  # init self.template_vars

        # pre_compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()  # init the above constraints

        # print(self.template_cnt_init_and_post)
        # print(self.template_cnt_trans)

    def add_template_vars(self):
        """
        Initialize self.template_vars
        E.g., assume that self.sts.variables are [x, y], and self.num_disjunctions = 2.
         Then, we will add two templates
            d1_0 + x*d1_1 + y*p1_2  == 0
                   OR
            d2_0 + x*d2_1 + y*d2_2  == 0
         NOTE: we always use self.num_templates = 1 by default. So, we do not consider
           the impact of self.num_templates here..
        After this function, self.template_vars will be:
        [[d1_0, d1_1, d1_2], [d2_0, d2_1, d2_2]]
        """
        for i in range(self.num_disjunctions):
            # the following is for creating d1_0, d2_0, ...
            if self.use_real:
                vars_for_dis = [z3.Real("d%d_%d" % (i + 1, 0))]
            else:
                vars_for_dis = [z3.Int("d%d_%d" % (i + 1, 0))]
            # creating d1_1, d1_2, d2_1, d2_2,...
            for j in range(1, self.arity + 1):
                if self.use_real:
                    vars_for_dis.append(z3.Real("d%d_%d" % (self.template_index, j)))
                else:
                    vars_for_dis.append(z3.Int("d%d_%d" % (self.template_index, j)))

            self.template_vars.append(vars_for_dis)
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

            cnts_init_post.append(term_init_post == 0)
            cnts_trans.append(term_trans == 0)

        self.template_cnt_init_and_post = big_or(cnts_init_post)
        self.template_cnt_trans = big_or(cnts_trans)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables: bool):
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
            cnts.append(term == 0)

        return big_or(cnts)
