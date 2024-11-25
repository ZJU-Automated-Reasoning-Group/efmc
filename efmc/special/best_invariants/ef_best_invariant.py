""" Generating Best Inductive Invariant via Exists-Forall Solving?

 TODO: this is an idea that combines the sprites of symbolic abstraction and constraint-based invariant generation.
  Perhaps a simple strategy is to use some kind of linear search:
  while true:
    Initialize the constraints for the template variables as P
    Try to generate an invariant I (e.g., using EFSMT solving to find solutions of P)
    if the previous step fails (P is unsatisfiable):
       break
    else:
       Update P by adding additional constraints to the template variables, which encodes "give me a more precise invariant"
    Essentially, we may need to solve a special kind of OMT instance:
    (1) The search space is characterized by a quantified formula; (2) the objective is about "most precise invariant"

 TODO: under certain conditions, we can use the symbolic abstraction based approach for computing the best inductive invariants.
   - i.e., symbolic abstraction + iteration (without using widening)
"""
import logging
# coding: utf-8
import time

import z3

from efmc.sts import TransitionSystem
from efmc.engines.ef.templates import TemplateType, BitVecIntervalTemplate
from efmc.utils import is_entail

logger = logging.getLogger(__name__)


class BestInvariantGenerator(object):
    # TODO: currently, we only use bv interval for PoC

    def __init__(self, sts: TransitionSystem):
        self.sts = sts
        self.ct = None  # template

    def set_template(self, ttype: str):
        assert "bv" in ttype
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

    def get_initial_invariant(self):
        """generate constraints about invariants"""
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

    def refine_invariant_condition(self):
        raise NotImplementedError

    def minimize_invairant(self):
        inv = self.get_initial_invariant()
        raise NotImplementedError
