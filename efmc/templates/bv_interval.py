# coding: utf-8
import z3

from .abstract_template import TemplateType, Template
from ..sts import TransitionSystem

"""
Interval domain over bit-vec
"""


class BitVecIntervalTemplate(Template):
    """
    TODO: infer the signess of variables? (or design a domain that is singness-irrelevant?
    """

    def __init__(self, sts: TransitionSystem):

        self.template_type = TemplateType.BV_INTERVAL

        self.sts = sts
        self.arity = len(self.sts.variables)

        self.template_vars = []  # vector of vector
        self.template_index = 0  # number of templates

        self.add_template_vars()

        # pre compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()

    def add_template_vars(self):
        """
        Add several groups of template vars
        """
        for var in self.sts.variables:
            tvars = [z3.BitVec("l_{}".format(str(var)), var.sort().size()),
                     z3.BitVec("u_{}".format(str(var)), var.sort().size())]
            self.template_vars.append(tvars)
            self.template_index += 1

    def get_additional_cnts_for_template_vars(self):
        """
        This implementation does not need additional ones?
        """
        return z3.BoolVal(True)

    def add_template_cnts(self) -> None:
        """
        Add cnts for init and post assertions (a trick)
        """
        cnts = []
        cnts_prime = []
        for i in range(self.arity):
            var = self.sts.variables[i]
            var_prime = self.sts.prime_variables[i]
            cnts.append(z3.And(z3.UGE(var, self.template_vars[i][0]), z3.ULE(var, self.template_vars[i][1])))
            cnts_prime.append(
                z3.And(z3.UGE(var_prime, self.template_vars[i][0]), z3.ULE(var_prime, self.template_vars[i][1])))

        self.template_cnt_init_and_post = z3.simplify(z3.And(cnts))
        self.template_cnt_trans = z3.simplify(z3.And(cnts_prime))

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """
        Build an invariant from a model (fixing the values of the template vars)
        """
        cnts = []
        for i in range(self.arity):
            if use_prime_variables:
                var = self.sts.prime_variables[i]
            else:
                var = self.sts.variables[i]
            tvar_l = self.template_vars[i][0]
            tvar_u = self.template_vars[i][1]
            cnts.append(z3.And(z3.UGE(var, model[tvar_l]), z3.ULE(var, model[tvar_u])))
        return z3.And(cnts)


class DisjunctiveBitVecIntervalTemplate(Template):
    """
    Disjunctive Interval domain
    """

    def __init__(self, sts: TransitionSystem):

        self.template_type = TemplateType.INTERVAL

        self.use_real = True

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
        for i in range(self.num_of_disjuncts):
            vars_for_dis = []
            for j in range(self.arity):
                var = self.sts.variables[j]
                self.template_index += 1
                tvars = [z3.BitVec("l_{}".format(str(var)), var.sort().size()),
                         z3.BitVec("u_{}".format(str(var)), var.sort().size())]
                vars_for_dis.append(tvars)

            self.template_vars.append(vars_for_dis)
        # print(self.template_vars)

    def get_additional_cnts_for_template_vars(self):
        return z3.BoolVal(True)

    def add_template_cnts(self) -> None:
        # FIXME: the following is from IntervalTemplate
        cnt_init_and_post_dis = []
        cnt_trans_dis = []
        for vars_for_dis in self.template_vars:
            # print("XXX", vars_for_dis)
            cnts_init_post = []  # For sts.variables
            cnts_trans = []  # For sts.prime_variables
            for i in range(self.arity):
                var = self.sts.variables[i]  # x, y
                prime_var = self.sts.prime_variables[i]  # x!, y!
                template_vars_for_var = vars_for_dis[i]  # TODO: is this correct?

        self.template_cnt_init_and_post = z3.Or(cnt_init_and_post_dis)
        self.template_cnt_trans = z3.Or(cnt_trans_dis)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        raise NotImplementedError
        # FIXME: the following is from IntervalTemplate
