# coding: utf-8
"""
Constraint/template based invariant inference using EFSMT solving
NOTE:
 - We assume there is only one invariant to be synthesized
 - This file relies heavily on the templates in efmc.templates
"""

import logging
import time
from enum import Enum

import z3

from efmc.smttools.efsmt_solver import EFSMTSolver
from efmc.sts import TransitionSystem
from efmc.templates import *
# PolyTemplate, IntervalTemplate, ZoneTemplate, OctagonTemplate, DisjunctivePolyTemplate, TemplateType, \
#    DisjunctiveIntervalTemplate, BitVecIntervalTemplate, DisjunctiveBitVecIntervalTemplate

logger = logging.getLogger(__name__)


def is_entail(a: z3.ExprRef, b: z3.ExprRef) -> bool:
    """Decide whether a entails b or not (i.e., b is a consequence of a)"""
    s = z3.Solver()
    s.add(z3.Not(z3.Implies(a, b)))
    if s.check() == z3.sat:
        return False
    else:
        return True


class EFSMTEngine(Enum):
    """
    Engines for solving the EFSMT instances
    """
    Z3 = 0  # use z3
    CVC5 = 1  # via the smtlib_solver interface
    YICES2 = 2  # via the smtlib_solver interface
    CEGAR = 3  # smt-based cegar-style algorithm (currently, we use z3' API)
    QBF = 4  # reduce to QBF: only applicable to BV instances
    SAT = 5  # reduce to SAT (QBF + QE?): only applicable to BV instances


class EFProver:
    """
    Exists-Forall SMT Solving for Inductive Invariant Inference
    """

    def __init__(self, sts: TransitionSystem):
        self.sts = sts # the transition system
        self.ct = None  # template type
        # ignoring the post condition
        # useful in "purely" invariant generation mode
        self.ignore_post_cond = False
        self.logic = "ALL" # the logic
        self.engine = EFSMTEngine.Z3

    def set_template(self, template_name: str):
        """Set self.ct (the template to use)"""
        if template_name == "poly":
            self.ct = PolyTemplate(self.sts)
        elif template_name == "interval":
            self.ct = IntervalTemplate(self.sts)
            # the following one uses a < x < b, c < y < d
            # need to confirm whether it is weaker...
            # self.ct = IntervalTemplateV2(self.sts)
        elif template_name == "zone":
            if len(self.sts.variables) < 2:
                self.ct = IntervalTemplate(self.sts)
            else:
                self.ct = ZoneTemplate(self.sts)
        elif template_name == "octagon":
            if len(self.sts.variables) < 2:
                self.ct = IntervalTemplate(self.sts)
            else:
                self.ct = OctagonTemplate(self.sts)
        elif template_name == "power_poly":  # bounded, disjunctive polyhedral
            self.ct = DisjunctivePolyTemplate(self.sts)
        elif template_name == "power_interval": # bounded, disjunctive interval
            self.ct = DisjunctiveIntervalTemplate(self.sts)
        # the following domains are for bit-vector programs
        elif template_name == "bv_interval":
            self.ct = BitVecIntervalTemplate(self.sts)
        elif template_name == "power_bv_interval":
            self.ct = DisjunctiveBitVecIntervalTemplate(self.sts)
        else:
            self.ct = PolyTemplate(self.sts)

        self.setup_logic()

    def setup_logic(self):
        """Setup self.logic according to the types of the template and the transition system.
        Another strategy is to use the get_logic API to analyze the constructed
        verification condition (it relies on several Probes of z3).
        """
        if self.sts.has_bv:
            self.logic = "BV"  # of UFBV?
        elif self.sts.has_real:
            template = self.ct.template_type
            if template == TemplateType.ZONE or template == TemplateType.INTERVAL \
                    or template == TemplateType.DISJUNCTIVE_INTERVAL:
                # FIXME: currently, our encoding seems to be non-linear...
                #   See the coe in efmc/templates/interval.val
                self.logic = "UFLRA"  # or LRA?
            else:
                self.logic = "UFNRA"  # or UFNRA?
        elif self.sts.has_int:
            template = self.ct.template_type
            if template == TemplateType.ZONE or template == TemplateType.INTERVAL:
                self.logic = "LIA"  # or UFLIA?
            else:
                self.logic = "NIA"  # or UFNIA?
        else:
            raise NotImplementedError

    def check_invariant(self, inv: z3.ExprRef, inv_in_prime_variables: z3.ExprRef):
        """Check whether the generated invariant is correct"""
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
        if (not self.ignore_post_cond) and (not is_entail(inv, self.sts.post)):
            correct = False
            print("Post not good!")

        if not correct:
            print("Init: ", self.sts.init)
            print("Trans: ", self.sts.trans)
            print("Post: ", self.sts.post)
            print("Inv: ", inv)
        else:
            print("Invariant check success!")

    def solve(self) -> bool:
        """
        The interface for calling different engines
        """
        # return self.solve_with_cegar_efsmt()  # FIXME: seems very slow
        if self.engine == EFSMTEngine.Z3:
            return self.solve_with_z3()
        elif self.engine == EFSMTEngine.CEGAR:
            return self.solve_with_cegar_efsmt()
        else:
            return self.solve_with_z3()

    def generate_vc(self) -> z3.ExprRef:
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

        if not self.ignore_post_cond:
            s.add(z3.ForAll(self.sts.variables, z3.Implies(self.ct.template_cnt_init_and_post,
                                                           self.sts.post)))

        # Add additional cnts to restrict the template variables
        if self.ct.template_type == TemplateType.INTERVAL or self.ct.template_type == TemplateType.DISJUNCTIVE_INTERVAL or \
                self.ct.template_type == TemplateType.ZONE or self.ct.template_type == TemplateType.OCTAGON:
            s.add(self.ct.get_additional_cnts_for_template_vars())

        return z3.And(s.assertions())

    def generate_quantifier_free_vc(self) -> z3.ExprRef:
        """Generate the "QF-part" of the VC (quantifiers can be added later)"""
        s = z3.Solver()
        s.add(z3.Implies(self.sts.init, self.ct.template_cnt_init_and_post))

        s.add(z3.Implies(z3.And(self.ct.template_cnt_init_and_post, self.sts.trans),
                         self.ct.template_cnt_trans))
        if not self.ignore_post_cond:
            s.add(z3.Implies(self.ct.template_cnt_init_and_post,
                             self.sts.post))
        # Add additional cnts to restrict the template variables
        if self.ct.template_type != TemplateType.POLYHEDRON:
            s.add(self.ct.get_additional_cnts_for_template_vars())

        return z3.And(s.assertions())

    def generate_vc2(self) -> z3.ExprRef:
        """Generate VC in the form of ForAll([allvars], And(Init,Trans,Post))
        It will first use self.generate_quantifier_free_vc to generate the QF part
        """
        qf_vc = self.generate_quantifier_free_vc()
        # Add additional cnts to restrict the template variables
        if self.ct.template_type != TemplateType.POLYHEDRON:
            qf_vc = z3.And(qf_vc, self.ct.get_additional_cnts_for_template_vars())

        # qf_vc = ctx_simplify(qf_vc) # can be slow

        return z3.ForAll(self.sts.all_variables, qf_vc)

    def solve_with_cegar_efsmt(self) -> bool:
        """This can be slow (perhaps not a good idea for NRA) Maybe good for LRA or BV?"""
        phi = self.generate_quantifier_free_vc()
        y = self.sts.all_variables
        ef_sol = EFSMTSolver(self.logic)
        print("User-defined EFSMT starting!!!")
        start = time.time()
        check_res, model = ef_sol.solve_with_cegar(y, phi)
        if check_res == z3.sat:
            print("User-defined EFSMT success time: ", time.time() - start)
            # FIXME: is this model OK?
            inv = z3.simplify(self.ct.build_invariant_expr(model))
            inv_in_prime_variables = z3.simplify(self.ct.build_invariant_expr(model, use_prime_variables=True))
            print("Invariant: ", inv)
            self.check_invariant(inv, inv_in_prime_variables)
            return True
        else:
            print("User-defined EFSMT fails time: ", time.time() - start)
            return False

    def solve_with_z3(self) -> bool:
        """This is the main entrance for the verification"""
        s = z3.SolverFor(self.logic)
        vc = self.generate_vc2()
        # print("Logic of VC: ", get_logic(z3.AndThen(z3.Tactic("simplify"),z3.Tactic("ctx-simplify"))(vc).as_expr()))
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
            inv = self.ct.build_invariant_expr(m, use_prime_variables=False)
            inv_in_prime_variables = self.ct.build_invariant_expr(m, use_prime_variables=True)
            print("Invariant: ", inv)
            self.check_invariant(inv, inv_in_prime_variables)
            return True
        else:
            print("EFSMT fail time: ", time.time() - start)
            print("Cannot verify using the template!")
            print(check_res)
            if check_res == z3.unknown:
                print(s.reason_unknown())
            return False

    def solve_with_bin_solver(self) -> z3.CheckSatResult:
        """Use a third party SMT solvers (perhaps in parallel)"""
        ef_sol = EFSMTSolver(self.logic)
        print("External binary solver starting!!!")
        y = self.sts.all_variables
        phi = self.generate_quantifier_free_vc()
        ef_sol.solve_with_bin_smt(y, phi)
