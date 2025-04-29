"""Interval template over bit-vector variables
"""

from efmc.engines.ef.templates.abstract_template import *
from efmc.utils.bv_utils import Signedness
from efmc.sts import TransitionSystem
from efmc.utils import big_and


class BitVecIntervalTemplate(Template):

    def __init__(self, sts: TransitionSystem, **kwargs):

        self.template_type = TemplateType.BV_INTERVAL

        # TODO: infer the signedness of variables? (or design a domain that is
        #  signedness-irrelevant. Currently, we use unsigned by default
        if sts.signedness == "signed":
            self.signedness = Signedness.SIGNED
        elif sts.signedness == "unsigned":
            self.signedness = Signedness.UNSIGNED

        self.sts = sts
        self.arity = len(self.sts.variables)

        # self.obj_no_overflow = kwargs.get("no_overflow", False)
        # self.obj_no_underflow = kwargs.get("no_underflow", False)

        self.template_vars = []  # vector of vector
        self.template_index = 0  # number of templates

        self.add_template_vars()

        # pre compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()

    def add_template_vars(self):
        """Add several groups of template variables"""
        for var in self.sts.variables:
            tvars = [z3.BitVec("l_{}".format(str(var)), var.sort().size()),
                     z3.BitVec("u_{}".format(str(var)), var.sort().size())]
            self.template_vars.append(tvars)

    def get_additional_cnts_for_template_vars(self):
        """ This implementation does not need additional ones"""
        return z3.BoolVal(True)

    def add_template_cnts(self) -> None:
        """Add cnts for init and post assertions (a trick)"""
        cnts = []
        cnts_prime = []
        for i in range(self.arity):
            var = self.sts.variables[i]
            var_prime = self.sts.prime_variables[i]
            var_l = self.template_vars[i][0]  # lower bound
            var_u = self.template_vars[i][1]  # upper bound

            if self.signedness == Signedness.UNSIGNED:
                cnts.append(z3.And(z3.UGE(var, var_l), z3.ULE(var, var_u)))
                cnts_prime.append(z3.And(z3.UGE(var_prime, var_l), z3.ULE(var_prime, var_u)))
            else:
                cnts.append(z3.And(var >= var_l, var <= var_u))
                cnts_prime.append(z3.And(var_prime >= var_l, var_prime <= var_u))

        self.template_cnt_init_and_post = z3.simplify(big_and(cnts))
        self.template_cnt_trans = z3.simplify(big_and(cnts_prime))

    def build_invariant(self, model: z3.ModelRef) -> z3.ExprRef:
        """Build an invariant from a model.
        
        Args:
            model: Z3 model containing values for template variables
            
        Returns:
            Z3 expression representing the invariant
        """
        return self.build_invariant_expr(model)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """ Build an invariant from a model (fixing the values of the template vars)"""
        constraints = []
        for i in range(self.arity):
            if use_prime_variables:
                var = self.sts.prime_variables[i]
            else:
                var = self.sts.variables[i]
            tvar_l = self.template_vars[i][0]
            tvar_u = self.template_vars[i][1]
            if self.signedness == Signedness.UNSIGNED:
                constraints.append(z3.And(z3.UGE(var, model[tvar_l]), z3.ULE(var, model[tvar_u])))
            else:
                constraints.append(z3.And(var >= model[tvar_l], var <= model[tvar_u]))
        return z3.And(constraints)


class DisjunctiveBitVecIntervalTemplate(Template):
    """
    Disjunctive Interval domain
    """

    def __init__(self, sts: TransitionSystem, **kwargs):

        self.template_type = TemplateType.BV_DISJUNCTIVE_INTERVAL

        # TODO: infer the signedness of variables? (or design a domain that is signedness-irrelevant
        if sts.signedness == "signed":
            self.signedness = Signedness.SIGNED
        elif sts.signedness == "unsigned":
            self.signedness = Signedness.UNSIGNED

        self.sts = sts
        self.arity = len(self.sts.variables)

        self.template_vars = []  # vector of vector
        self.template_index = 0  # number of templates

        self.num_disjunctions = kwargs.get("num_disjunctions", 2)

        self.add_template_vars()

        # pre compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()

    def add_template_vars(self):
        for i in range(self.num_disjunctions):
            vars_for_dis = []
            for j in range(self.arity):
                var = self.sts.variables[j]
                tvars = [z3.BitVec("d{0}_{1}_l".format(i, str(var)), var.sort().size()),
                         z3.BitVec("d{0}_{1}_u".format(i, str(var)), var.sort().size())]
                vars_for_dis.append(tvars)

            self.template_vars.append(vars_for_dis)
        # print(self.template_vars)

    def get_additional_cnts_for_template_vars(self):
        return z3.BoolVal(True)

    def add_template_cnts(self) -> None:
        # FIXME: the following is from IntervalTemplate
        cnt_init_and_post_dis = []
        cnt_trans_dis = []

        for i in range(self.num_disjunctions):
            # Invariant: len(self.template_vars) = self.num_disjunctions
            # print("XXX", vars_for_dis)
            cnt_init_post = []  # For sts.variables
            cnt_trans = []  # For sts.prime_variables
            for j in range(self.arity):
                var = self.sts.variables[j]  # e.g., x, y
                prime_var = self.sts.prime_variables[j]  # e.g., x!, y!
                template_vars_for_var = self.template_vars[i][j]
                if self.signedness == Signedness.UNSIGNED:
                    cnt_init_post.append(
                        z3.And(z3.UGE(var, template_vars_for_var[0]),
                               z3.ULE(var, template_vars_for_var[1])))
                    cnt_trans.append(
                        z3.And(z3.UGE(prime_var, template_vars_for_var[0]),
                               z3.ULE(prime_var, template_vars_for_var[1])))
                else:
                    cnt_init_post.append(
                        z3.And(var >= template_vars_for_var[0], var <= template_vars_for_var[1]))
                    cnt_trans.append(
                        z3.And(prime_var >= template_vars_for_var[0], prime_var <= template_vars_for_var[1]))

            cnt_init_and_post_dis.append(big_and(cnt_init_post))
            cnt_trans_dis.append(big_and(cnt_trans))

        self.template_cnt_init_and_post = z3.Or(cnt_init_and_post_dis)
        self.template_cnt_trans = z3.Or(cnt_trans_dis)
        # print(self.template_cnt_init_and_post)
        # print(self.template_cnt_trans)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        # TODO: check for correctness
        cnts_dis = []
        for vars_for_dis in self.template_vars:
            cnts = []
            for i in range(self.arity):
                if use_prime_variables:
                    var = self.sts.prime_variables[i]
                else:
                    var = self.sts.variables[i]
                template_vars_for_var = vars_for_dis[i]
                lower, upper = template_vars_for_var[0], template_vars_for_var[1]
                if self.signedness == Signedness.UNSIGNED:
                    cnts.append(z3.And(z3.UGE(var, model[lower]), z3.ULE(var, model[upper])))
                else:
                    cnts.append(z3.And(var >= model[lower], var <= model[upper]))

            cnts_dis.append(big_and(cnts))

        return z3.Or(cnts_dis)

    def build_invariant(self, model: z3.ModelRef) -> z3.ExprRef:
        """Build an invariant from a model.
        
        Args:
            model: Z3 model containing values for template variables
            
        Returns:
            Z3 expression representing the invariant
        """
        return self.build_invariant_expr(model)
