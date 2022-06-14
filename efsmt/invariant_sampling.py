# coding: utf-8
import time
import logging
import z3
from .sts import TransitionSystem
from .templates import TemplateType, BitVecIntervalTemplate
from .utils import is_entail

"""
Sampling (least) inductive invariant via Symbolic Abstraction

"""


logger = logging.getLogger(__name__)


class InvariantSampler(object):
    # TODO: currently, we only use bv interval for PoC

    def __init__(self, sts: TransitionSystem):
        self.sts = sts
        self.ct = None  # template

    def set_template(self, ttype: str):
        assert ttype == "bv_interval"
        self.ct = BitVecIntervalTemplate(self.sts)

    def check_invariant(self, inv: z3.ExprRef, inv_in_prime_variables: z3.ExprRef):
        """
        Check whether the generated invariant is correct
        """
        correct = True

        # 1. Init
        if not is_entail(self.sts.init, inv):
            correct = False
            print("Init wrong!")

        # 2. Inductive
        if not is_entail(z3.And(self.sts.trans, inv), inv_in_prime_variables):
            correct = False
            print("Inductive wrong!")

        # 3. Post
        if not is_entail(inv, self.sts.post):
            correct = False
            print("Post not good!")

        if not correct:
            print("Init: ", self.sts.init)
            print("Trans: ", self.sts.trans)
            print("Post: ", self.sts.post)
            print("Inv: ", inv)
        else:
            print("Invariant check success!")

    def generate_invariant_condition(self):
        """
        """
        s = z3.Solver()
        s.add(z3.Implies(self.sts.init, self.ct.template_cnt_init_and_post))

        s.add(z3.Implies(z3.And(self.ct.template_cnt_init_and_post, self.sts.trans),
                         self.ct.template_cnt_trans))

        # For now, do not consider post-condition
        # s.add(z3.Implies(self.ct.template_cnt_init_and_post, self.sts.post))

        qf_cond = z3.And(s.assertions())

        return z3.ForAll(self.sts.all_variables, qf_cond)

    def get_one_invariant(self):
        assert self.ct.template_type == TemplateType.BV_INTERVAL
        s = z3.SolverFor("UFBV")
        inv_cond = self.generate_invariant_condition()
        s.add(inv_cond)  # sometimes can be much faster!
        print("EFSMT starting!!!")
        start = time.time()
        check_res = s.check()
        if check_res == z3.sat:
            print("EFSMT success time: ", time.time() - start)
            m = s.model()
            print(m)
            # for Debugging
            # print("\nTemplate and the founded values: ")
            # print(" ", self.ct.get_template_cnt_init_and_post())
            # print("  model:", m)
            inv = self.ct.build_invariant_expr(m, use_prime_variables=False)
            inv_in_prime_variables = self.ct.build_invariant_expr(m, use_prime_variables=True)
            print("Invariant: ", inv)
            self.check_invariant(inv, inv_in_prime_variables)
            return True
        else:
            print("EFSMT fail time: ", time.time() - start)
            # print("Cannot verify using the template!")

            if check_res == z3.unknown:
                print(s.reason_unknown())
            return False

    def minimize_invairant(self):

        return
