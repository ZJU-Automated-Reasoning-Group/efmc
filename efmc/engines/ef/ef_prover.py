# coding: utf-8
"""
Constraint/template based invariant inference using EFSMT solving
NOTE:
 - We assume there is only one invariant to be synthesized.
 - This file relies heavily on the templates in efmc.templates
"""

import logging
import time
from enum import Enum

import z3

from efmc.sts import TransitionSystem
from efmc.utils import is_entail
from efmc.engines.ef.templates import *
from efmc.engines.ef.efsmt.efsmt_solver import EFSMTSolver

logger = logging.getLogger(__name__)


class EFProver:
    """
    Exists-Forall SMT Solving for Inductive Invariant Inference
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts  # the transition system
        self.ct = None  # template type
        self.ignore_post_cond = False  # ignoring the post condition (useful in "purely" invariant generation mode)
        self.logic = "ALL"  # the logic, e.g., BV, LIA, ...
        self.validate_invaraint = True  # use SMT solvers to validate the correctness of the invariant
        self.inductive_invaraint = None  # the generated invariant (e.g., to be used by other engines)
        self.property_strengthening = False  # use "template = P and template" as the invariant template
        self.seed = kwargs.get("seed", 1)  # random seed
        self.engine = "z3api"   # Use Z3's Python API (for testing features)

    def set_engine(self, engine_name: str):
        self.engine = engine_name

    def set_template(self, template_name: str):
        """Set self.ct (the template to use)"""
        if template_name == "poly":
            self.ct = PolyTemplate(self.sts)
        elif template_name == "power_poly":  # bounded, disjunctive polyhedral
            self.ct = DisjunctivePolyTemplate(self.sts)
        elif template_name == "interval":
            self.ct = IntervalTemplate(self.sts)
            # the following one uses a < x < b, c < y < d
            # need to confirm whether it is weaker...
            # self.ct = IntervalTemplateV2(self.sts)
        elif template_name == "power_interval":  # bounded, disjunctive interval
            self.ct = DisjunctiveIntervalTemplate(self.sts)
        elif template_name == "zone":
            if len(self.sts.variables) < 2:
                self.ct = IntervalTemplate(self.sts)
            else:
                self.ct = ZoneTemplate(self.sts)
        # FIXME: add disjunctive zone
        elif template_name == "octagon":
            if len(self.sts.variables) < 2:
                self.ct = IntervalTemplate(self.sts)
            else:
                self.ct = OctagonTemplate(self.sts)
        # FIXME: add disjunctive octagon
        # the following domains are for bit-vector programs
        elif template_name == "bv_interval":
            self.ct = BitVecIntervalTemplate(self.sts)
        elif template_name == "power_bv_interval":
            self.ct = DisjunctiveBitVecIntervalTemplate(self.sts)
        elif template_name == "bv_zone":
            if len(self.sts.variables) < 2:
                self.ct = BitVecIntervalTemplate(self.sts)
            else:
                self.ct = BitVecZoneTemplate(self.sts)
        elif template_name == "power_bv_zone":
            self.ct = DisjunctiveBitVecIntervalTemplate(self.sts)
        elif template_name == "bv_octagon":
            if len(self.sts.variables) < 2:
                self.ct = BitVecIntervalTemplate(self.sts)
            else:
                self.ct = BitVecOctagonTemplate(self.sts)
        elif template_name == "power_bv_octagon":
            self.ct = DisjunctiveBitVecOctagonTemplate(self.sts)
        elif template_name == "bv_affine":
            self.ct = BitVecAffineTemplate(self.sts)
        elif template_name == "power_bv_affine":
            self.ct = DisjunctiveBitVecAffineTemplate(self.sts)
        elif template_name == "bv_poly":
            self.ct = BitVecPolyhedronTemplate(self.sts)
        elif template_name == "power_bv_poly":
            self.ct = DisjunctiveBitVecPolyhedronTemplate(self.sts)
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
        """The interface for calling different engines"""
        print("Start solving: ")
        print("Used template: {}".format(str(self.ct.template_type)))
        print("Used logic: {}".format(str(self.logic)))
        # return self.solve_with_cegar_efsmt()  # FIXME: seems very slow
        if self.engine == "z3api":
            return self.solve_with_z3()
        else:
            qf_vc = self.generate_quantifier_free_vc()
            print("EFSMT starting!!!")
            ef_solver = EFSMTSolver(logic=self.logic, solver=self.engine)
            forall_vars = self.sts.all_variables
            exists_vars = []
            for ele in self.ct.template_vars:
                if isinstance(ele, list):
                    for v in ele: exists_vars.append(v)
                else:
                    exists_vars.append(ele)
            # print("qf part of vc: ", qf_vc)
            # print("exists vars: ", exists_vars)
            # print("forall vars: ", forall_vars)
            ef_solver.init(exist_vars=exists_vars, forall_vars=forall_vars, phi=qf_vc)
            return ef_solver.solve()

    def generate_vc(self) -> z3.ExprRef:
        """ Generate VC (Version 1)
        Another strategy is to generate the quantifier free body first and then add the
        quantifier once (to self.sts.all_variables), which is implemented in generate_vc2
        """
        s = z3.Solver()
        if self.property_strengthening:
            # use "template = P and template" as the invariant template
            var_map = []  # x' to x, y' to y
            for i in range(len(self.sts.variables)):
                var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            post_in_prime = z3.substitute(self.sts.post, var_map)  # post cond that uses x', y', ..

            s.add(z3.ForAll(self.sts.variables, z3.Implies(self.sts.init,
                                                           z3.And(self.sts.post, self.ct.template_cnt_init_and_post))))
            s.add(z3.ForAll(self.sts.all_variables,
                            z3.Implies(z3.And(self.sts.post, self.ct.template_cnt_init_and_post, self.sts.trans),
                                       z3.And(post_in_prime, self.ct.template_cnt_trans))))
            if not self.ignore_post_cond:
                s.add(z3.ForAll(self.sts.variables,
                                z3.Implies(z3.And(self.sts.post, self.ct.template_cnt_init_and_post),
                                           self.sts.post)))
        else:
            s.add(z3.ForAll(self.sts.variables, z3.Implies(self.sts.init, self.ct.template_cnt_init_and_post)))
            s.add(z3.ForAll(self.sts.all_variables,
                            z3.Implies(z3.And(self.ct.template_cnt_init_and_post, self.sts.trans),
                                       self.ct.template_cnt_trans)))
            if not self.ignore_post_cond:
                s.add(z3.ForAll(self.sts.variables, z3.Implies(self.ct.template_cnt_init_and_post,
                                                               self.sts.post)))

        # Add additional cnts to restrict the template variables (only for int/real)
        if self.ct.template_type == TemplateType.INTERVAL or \
                self.ct.template_type == TemplateType.DISJUNCTIVE_INTERVAL or \
                self.ct.template_type == TemplateType.ZONE or self.ct.template_type == TemplateType.OCTAGON:
            s.add(self.ct.get_additional_cnts_for_template_vars())

        return z3.And(s.assertions())

    def generate_quantifier_free_vc(self) -> z3.ExprRef:
        """Generate the "QF-part" of the VC (quantifiers will be added later
         by the generate_vc2 function)"""
        s = z3.Solver()
        if self.property_strengthening:
            # use "template = P and template" as the invariant template!!
            var_map = []  # x' to x, y' to y
            for i in range(len(self.sts.variables)):
                var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            post_in_prime = z3.substitute(self.sts.post, var_map)  # post cond that uses x', y', ..

            s.add(z3.ForAll(self.sts.variables, z3.Implies(self.sts.init,
                                                           z3.And(self.sts.post, self.ct.template_cnt_init_and_post))))
            s.add(z3.ForAll(self.sts.all_variables,
                            z3.Implies(z3.And(self.sts.post, self.ct.template_cnt_init_and_post, self.sts.trans),
                                       z3.And(post_in_prime, self.ct.template_cnt_trans))))
            if not self.ignore_post_cond:
                s.add(z3.ForAll(self.sts.variables,
                                z3.Implies(z3.And(self.sts.post, self.ct.template_cnt_init_and_post),
                                           self.sts.post)))
        else:
            s.add(z3.Implies(self.sts.init, self.ct.template_cnt_init_and_post))

            s.add(z3.Implies(z3.And(self.ct.template_cnt_init_and_post, self.sts.trans),
                             self.ct.template_cnt_trans))

            if not self.ignore_post_cond:
                s.add(z3.Implies(self.ct.template_cnt_init_and_post,
                                 self.sts.post))

        # Add additional cnts to restrict the template variables
        if self.ct.template_type == TemplateType.INTERVAL or \
                self.ct.template_type == TemplateType.DISJUNCTIVE_INTERVAL or \
                self.ct.template_type == TemplateType.ZONE or self.ct.template_type == TemplateType.OCTAGON:
            s.add(self.ct.get_additional_cnts_for_template_vars())

        return z3.And(s.assertions())

    def generate_vc2(self) -> z3.ExprRef:
        """Generate VC in the form of ForAll([allvars], And(Init,Trans,Post))
        It will first use self.generate_quantifier_free_vc to generate the QF part
        """
        qf_vc = self.generate_quantifier_free_vc()
        # Add additional cnts to restrict the template variables
        # if self.ct.template_type != TemplateType.POLYHEDRON:
        #    qf_vc = z3.And(qf_vc, self.ct.get_additional_cnts_for_template_vars())
        # qf_vc = ctx_simplify(qf_vc) # can be slow
        logger.debug("Finish generating VC")
        return z3.ForAll(self.sts.all_variables, qf_vc)

    def solve_with_z3(self) -> bool:
        """This is the main entrance for the verification"""
        s = z3.SolverFor(self.logic)
        vc = self.generate_vc2()
        # TODO: use the interface in efsmt/efsmt_solver.py
        #     e.g., pass the following y and phi to EFSMTSolver
        #       y = self.sts.all_variables
        #       phi = self.generate_quantifier_free_vc()
        #     One possible problem is: to build the invariant, we need a model, which
        #     may not be very easy to be parsed if we use a bin solver
        # print(vc)
        s.add(vc)  # sometimes can be much faster!
        print("EFSMT starting!!!")
        start = time.time()
        # print(s)
        # print(s.to_smt2())
        check_res = s.check()
        if check_res == z3.sat:
            print("EFSMT success time: ", time.time() - start)
            m = s.model()
            if self.property_strengthening:
                # use "template = P and template" as the invariant template
                inv = z3.And(self.sts.post, self.ct.build_invariant_expr(m, use_prime_variables=False))
                print("Invariant: ", inv)
                if self.validate_invaraint:
                    var_map = []  # x' to x, y' to y
                    for i in range(len(self.sts.variables)):
                        var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
                    post_in_prime = z3.substitute(self.sts.post, var_map)  # post cond that uses x', y', ..
                    inv_in_prime_variables = z3.And(post_in_prime,
                                                    self.ct.build_invariant_expr(m, use_prime_variables=True))
                    self.check_invariant(inv, inv_in_prime_variables)
            else:
                inv = self.ct.build_invariant_expr(m, use_prime_variables=False)
                print("Invariant: ", inv)
                if self.validate_invaraint:
                    inv_in_prime_variables = self.ct.build_invariant_expr(m, use_prime_variables=True)
                    self.check_invariant(inv, inv_in_prime_variables)
            self.inductive_invaraint = inv  # preserve the invariant
            return True
        else:
            print("EFSMT fail time: ", time.time() - start)
            print("Cannot verify using the template!")
            print(check_res)
            if check_res == z3.unknown:
                print(s.reason_unknown())
            return False
