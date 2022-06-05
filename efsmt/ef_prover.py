# coding: utf-8
import time
# from typing import List
from enum import Enum

import z3

from .smttools.efsmt_solver import efsmt_solve_aux
# from .smttools.pysmt_solver import PySMTSolver
from .smttools.smtlib_solver import SMTLIBSolver
from .sts import TransitionSystem
from .templates import PolyTemplate, IntervalTemplate, ZoneTemplate, DisjunctivePolyTemplate, TemplateType, \
    DisjunctiveIntervalTemplate, BitVecIntervalTemplate
from .utils import is_entail

# TODO: add a few simple unit tests

"""
Generate template-based invariants using EF-SMT solving
NOTE:
- We assume there is only one invariant to be synthesized
"""


class EFSMTSolverType(Enum):
    Z3 = 0
    CVC5 = 1
    MATHSAT5 = 2


class EFProver:
    """
    Exists-Forall Solving for Invariant Inference
    """

    def __init__(self, sts: TransitionSystem):
        self.sts = sts
        self.ct = None  # template

    def set_template(self, ttype: str):
        if ttype == "poly":
            self.ct = PolyTemplate(self.sts)
        elif ttype == "interval":
            self.ct = IntervalTemplate(self.sts)
            # the following one uses a < x < b, c < y < d
            # need to confirm whether it is weaker...
            # self.ct = IntervalTemplateV2(self.sts)
        elif ttype == "zone":
            if len(self.sts.variables) < 2:
                self.ct = IntervalTemplate(self.sts)
            else:
                self.ct = ZoneTemplate(self.sts)
        elif ttype == "power_poly":
            self.ct = DisjunctivePolyTemplate(self.sts)
        elif ttype == "power_interval":
            self.ct = DisjunctiveIntervalTemplate(self.sts)
        elif ttype == "bv_interval":
            self.ct = BitVecIntervalTemplate(self.sts)
        else:
            self.ct = PolyTemplate(self.sts)

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

    def solve(self):
        # return self.solve_with_cegar_efsmt()  # FIXME: seems very slow
        return self.solve_with_z3()

    def generate_vc(self):
        """
        Generate VC
        TODO: another strategy is to generate the quantifier free body first,
        and then add the quantifier once (using self.sts.all_variables?)
        """
        s = z3.Solver()
        s.add(z3.ForAll(self.sts.variables, z3.Implies(self.sts.init,
                                                       self.ct.template_cnt_init_and_post)))

        s.add(z3.ForAll(self.sts.all_variables, z3.Implies(z3.And(self.ct.template_cnt_init_and_post, self.sts.trans),
                                                           self.ct.template_cnt_trans)))

        s.add(z3.ForAll(self.sts.variables, z3.Implies(self.ct.template_cnt_init_and_post,
                                                       self.sts.post)))

        # Add additional cnts to restrict the template variables
        if self.ct.template_type != TemplateType.POLYHEDRON:
            s.add(self.ct.get_additional_cnts_for_template_vars())

        return z3.And(s.assertions())

    def generate_quantifier_free_vc(self):
        """
        This is used by efsmt_solve (a tiny CEGAR-style algorithm)
        """
        s = z3.Solver()
        s.add(z3.Implies(self.sts.init, self.ct.template_cnt_init_and_post))

        s.add(z3.Implies(z3.And(self.ct.template_cnt_init_and_post, self.sts.trans),
                         self.ct.template_cnt_trans))
        s.add(z3.Implies(self.ct.template_cnt_init_and_post,
                         self.sts.post))
        # Add additional cnts to restrict the template variables
        if self.ct.template_type != TemplateType.POLYHEDRON:
            s.add(self.ct.get_additional_cnts_for_template_vars())

        return z3.And(s.assertions())

    def generate_vc2(self):
        """
        ForAll([allvars], And(Init,Trans,Post))
        """
        qf_vc = self.generate_quantifier_free_vc()
        # Add additional cnts to restrict the template variables
        if self.ct.template_type != TemplateType.POLYHEDRON:
            qf_vc = z3.And(qf_vc, self.ct.get_additional_cnts_for_template_vars())

        # qf_vc = ctx_simplify(qf_vc) # can be slow

        return z3.ForAll(self.sts.all_variables, qf_vc)

    def solve_with_cegar_efsmt(self):
        """
        This can be slow (perhaps not a good idea for QF_NRA)
        Maybe QF_LRA or QF_BV?
        """
        phi = self.generate_quantifier_free_vc()
        print("User-defined EFSMT starting!!!")
        start = time.time()
        # print(self.sts.all_variables)
        z3_res, model = efsmt_solve_aux(self.sts.all_variables, phi)
        if z3_res == z3.sat:
            print("User-defined EFSMT success time: ", time.time() - start)
            # print("\nTemplate and the founded values: ")
            # print(" ", self.ct.template_cnt_init_and_post)
            print("  model:", model)
            # FIXME: is this model OK?
            inv = z3.simplify(self.ct.build_invariant_expr(model))
            inv_in_prime_variables = z3.simplify(self.ct.build_invariant_expr(model, use_prime_variables=True))
            print("Invariant: ", inv)
            self.check_invariant(inv, inv_in_prime_variables)
            return True
        else:
            print("User-defined EFSMT fails time: ", time.time() - start)
            return False

    def solve_with_z3(self):
        if self.ct.template_type == TemplateType.ZONE or self.ct.template_type == TemplateType.INTERVAL:
            s = z3.SolverFor("UFLRA")  # FIXME: our encoding seems to be non-linear...
        elif self.ct.template_type == TemplateType.BV_INTERVAL:
            s = z3.SolverFor("UFBV")
        else:
            s = z3.SolverFor("UFNRA")
        vc = self.generate_vc2()
        # print("Logic of VC: ", get_logic(z3.AndThen(z3.Tactic("simplify"), z3.Tactic("ctx-simplify"))(vc).as_expr()))
        # vc = self.generate_vc()
        s.add(vc)  # sometimes can be much faster!
        print("EFSMT starting!!!")
        start = time.time()
        # print(s)
        # print(s.to_smt2())
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
            print("Cannot verify using the template!")

            if check_res == z3.unknown:
                print(s.reason_unknown())
            return False

    def solve_with_bin(self):
        """
        Use a third party SMT solvers (perhaps in parallel)
        """
        solver = z3.Solver()
        solver.add(self.generate_vc())
        if self.ct.template_type == TemplateType.ZONE or self.ct.template_type == TemplateType.INTERVAL:
            smt2sting = "(seg-logic UFLRA)\n"  #
        else:
            smt2sting = "(seg-logic UFNRA)\n"  #
        smt2sting += "\n".join(solver.to_smt2().split("\n"))
        # smt2sting += "\n".join(solver.to_smt2().split("\n")[:-2])  # for removing (check-sat)
        bin_cmd = f"/Users/prism/Work/cvc5/build/bin/cvc5 -q --produce-models"
        # bin_cmd = f"/Users/prism/Work/cvc5/build/bin/cvc5 -q --produce-models"
        bin_solver = SMTLIBSolver(bin_cmd)
        res = bin_solver.check_sat_from_scratch(smt2sting)
        ret = z3.unknown
        if res == "sat":
            # print(bin_solver.get_expr_values(["p1", "p0", "p2"]))
            ret = z3.sat
        elif res == "unsat":
            ret = z3.unsat
        bin_solver.stop()
        return ret
