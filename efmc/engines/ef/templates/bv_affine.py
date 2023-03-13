"""Affine relation domain over bit-vectors
"""
import z3
# from typing import List

from efmc.engines.ef.templates.abstract_template import TemplateType, Template
from efmc.sts import TransitionSystem
from efmc.engines.ef.templates.bv_utils import Signedness
from efmc.utils import big_and


class BitVecAffineTemplate(Template):
    """
    TODO: There are several variants. Some references
      - Matt elder et al., Abstract domains of affine relations, TOPLAS'14
      - Olm and Seidl, Precise interprocedural analysis through linear algebra, POPL'04
       - King and Sondergaard,
         Inferring congruence equations using SAT, CAV'08
         Automatic abstraction for congruences, VMCAI'10
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.template_type = TemplateType.BV_AFFINE

        self.sts = sts
        self.arity = len(self.sts.variables)

        if sts.signedness == "signed":
            self.signedness = Signedness.SIGNED
        elif sts.signedness == "unsigned":
            self.signedness = Signedness.UNSIGNED

        self.template_vars = []  # vector of vector

        self.template_index = 0

        #  number of linear inequalities (NOTE: interval, zone, and octagon domains do not need this)
        #  thus, the following field is polyhedron-specific
        self.num_templates = 1

        # FIXME: we assume all variables are bit-vectors, and they have the same size
        #  Otherwise, many operators (e.g., +, -) cannot be applied two variables directly.
        #  However, this is not a good idea for real-world cases
        self.bv_size = self.sts.variables[0].sort().size()

        self.add_template_vars()  # init self.template_vars

        # pre-compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()  # init the above constraints

    def add_template_vars(self):
        """
        Initialize self.template_vars

        E.g., assume that self.sts.variables are [x, y]. We will add two templates
            p1_0 + x*p1_1 + y*p1_2  == 0
            p2_0 + x*p2_1 + y*p2_2  == 0

        After this function, self.template_vars will be:
        [[p1_0, p1_1, p1_2], [p2_0, p2_1, p2_2]]
        """
        for _ in range(self.num_templates):
            self.template_index += 1
            # the following is for creating p1_0, p2_0, ...
            tvars = [z3.BitVec("p%d_%d" % (self.template_index, 0), self.bv_size)]
            # creating p1_1, p1_2, p2_1, p2_2, ...
            for i in range(1, self.arity + 1):
                tvars.append(z3.BitVec("p%d_%d" % (self.template_index, i), self.bv_size))
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

            if self.signedness == Signedness.UNSIGNED:
                cnts_init_post.append(term_init_post == 0)
                cnts_trans.append(term_trans == 0)
            else:
                cnts_init_post.append(term_init_post == 0)
                cnts_trans.append(term_trans == 0)

        self.template_cnt_init_and_post = big_and(cnts_init_post)
        self.template_cnt_trans = big_and(cnts_trans)

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

            if self.signedness == Signedness.UNSIGNED:
                cnts.append(term == 0)
            else:
                cnts.append(term == 0)
        return big_and(cnts)


class DisjunctiveBitVecAffineTemplate(Template):
    """
    TODO: There are several different variants. Some references
      - Matt elder et al., Abstract domains of affine relations, TOPLAS'14
      - Olm and Seidl, Precise interprocedural analysis through linear algebra, POPL'04
       - King and Sondergaard,
         Inferring congruence equations using SAT, CAV'08
         Automatic abstraction for congruences, VMCAI'10
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.template_type = TemplateType.BV_DISJUNCTIVE_AFFINE

        if sts.signedness == "signed":
            self.signedness = Signedness.SIGNED
        elif sts.signedness == "unsigned":
            self.signedness = Signedness.UNSIGNED

        self.sts = sts

        self.num_disjunctions = kwargs.get("num_disjunctions", 2)

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
