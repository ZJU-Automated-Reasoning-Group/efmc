# coding: utf-8
"""
Constraint/template based invariant inference using EFSMT solving
NOTE:
 - We assume there is only one invariant to be synthesized
 - There is only one pair of <pre, post> from TransitionSystem
 - This file relies heavily on the templates in efmc.templates
"""

import logging
import time
# from enum import Enum
from typing import List, Dict, Any, Optional, Union, Tuple

import z3

from efmc.sts import TransitionSystem
from efmc.utils import is_entail
from efmc.engines.ef.templates import *
from efmc.engines.ef.efsmt.efsmt_solver import EFSMTSolver
from efmc.utils.z3_expr_utils import extract_all, ctx_simplify
from efmc.utils.verification_utils import VerificationResult, check_invariant

logger = logging.getLogger(__name__)


class EFProver:
    """
    Template-based invariant inference using exists-forall SMT solving.
    
    This class implements a template-based approach to invariant inference,
    where the invariant is assumed to have a specific form (template) with
    unknown parameters. The verification problem is then reduced to finding
    values for these parameters such that the resulting formula is an inductive
    invariant.
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts  # the transition system
        self.ct = None  # template type
        self.ignore_post_cond = False  # ignoring the post condition (useful in "purely" invariant generation mode)
        self.logic = "ALL"  # the logic, e.g., BV, LIA, ...
        self.inductive_invaraint = None  # the generated invariant (e.g., to be used by other engines)
        self.print_vc = False

        self.seed = kwargs.get("seed", 1)  # random seed
        # Use "template = P and template" as the actual invariant template (a simple strengthening strategy)
        self.prop_strengthening = kwargs.get("prop_strengthen", False)

        # abstraction refinement?
        self.abs_refine = kwargs.get("abs_refine", False)

        # The SMT solver for dealing with the EFSMT queries
        self.solver = kwargs.get("solver", "z3api")

        # Use SMT solvers to validate the correctness of the invariant
        self.validate_invariant = kwargs.get("validate_invariant",
                                             False)

        # Prevent over/underflow in the template exprs, e.g., x - y, x + y
        self.no_overflow = kwargs.get("no_overflow", False)
        self.no_underflow = kwargs.get("no_underflow", False)

        # We have a backend solving engine based on the pySMT library (a CEGIS-style algorithm that uses SMT oracle in pySMT)
        # Since pySMT allows for choosing different SMT backends, we add the following option.
        self.pysmt_solver = kwargs.get("pysmt_solver", "z3")

        print("prevent over/under flow? ", self.no_overflow, self.no_underflow)

    def set_solver(self, solver_name: str):
        self.solver = solver_name

    def set_template(self, template_name: str, num_disjunctions=2, **kwargs):
        """Set self.ct (the template to use)"""
        if self.sts.has_bv:
            # the following domains are for bit-vector programs
            if template_name == "bv_interval":
                self.ct = BitVecIntervalTemplate(self.sts)
            elif template_name == "power_bv_interval":
                self.ct = DisjunctiveBitVecIntervalTemplate(self.sts,
                                                            num_disjunctions=num_disjunctions)
            elif template_name == "bv_zone":
                if len(self.sts.variables) < 2:
                    self.ct = BitVecIntervalTemplate(self.sts)
                else:
                    self.ct = BitVecZoneTemplate(self.sts,
                                                 no_overflow=self.no_overflow,
                                                 no_underflow=self.no_underflow)
            elif template_name == "power_bv_zone":
                self.ct = DisjunctiveBitVecZoneTemplate(self.sts,
                                                        num_disjunctions=num_disjunctions,
                                                        no_overflow=self.no_overflow,
                                                        no_underflow=self.no_underflow)
            elif template_name == "bv_octagon":
                if len(self.sts.variables) < 2:
                    self.ct = BitVecIntervalTemplate(self.sts)
                else:
                    self.ct = BitVecOctagonTemplate(self.sts,
                                                    no_overflow=self.no_overflow,
                                                    no_underflow=self.no_underflow)
            elif template_name == "power_bv_octagon":
                self.ct = DisjunctiveBitVecOctagonTemplate(self.sts,
                                                           num_disjunctions=num_disjunctions,
                                                           no_overflow=self.no_overflow,
                                                           no_underflow=self.no_underflow)
            elif template_name == "bv_affine":
                self.ct = BitVecAffineTemplate(self.sts)
            elif template_name == "power_bv_affine":
                self.ct = DisjunctiveBitVecAffineTemplate(self.sts,
                                                          nnum_disjunctions=num_disjunctions)
            elif template_name == "bv_poly":
                self.ct = BitVecPolyhedronTemplate(self.sts)
            elif template_name == "power_bv_poly":
                self.ct = DisjunctiveBitVecPolyhedronTemplate(self.sts,
                                                              num_disjunctions=num_disjunctions)
            # TBD
            elif template_name == "knownbits":
                self.ct = KnownBitsTemplate(self.sts)
            elif template_name == "bitpredabs":
                self.ct = BitPredAbsTemplate(self.sts)
            elif template_name == "bv_enhanced_pattern":
                self.ct = EnhancedBitPatternTemplate(self.sts, **kwargs)
            else:
                raise NotImplementedError
        else:
            # The following templates are for integer or real programs
            if template_name == "interval":
                self.ct = IntervalTemplate(self.sts)
                # the following one uses a < x < b, c < y < d
                # need to confirm whether it is weaker...
                # self.ct = IntervalTemplateV2(self.sts)
            elif template_name == "power_interval":  # bounded, disjunctive interval
                self.ct = DisjunctiveIntervalTemplate(self.sts, num_disjunctions=num_disjunctions)
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
            elif template_name == "affine":
                self.ct = AffineTemplate(self.sts)
            elif template_name == "power_affine":
                self.ct = DisjunctiveAffineTemplate(self.sts, num_disjunctions=num_disjunctions)
            elif template_name == "poly":
                self.ct = PolyTemplate(self.sts)
            elif template_name == "power_poly":  # bounded, disjunctive polyhedral
                self.ct = DisjunctivePolyTemplate(self.sts, num_disjunctions=num_disjunctions)
            else:
                raise NotImplementedError

        self.setup_logic()

    def setup_logic(self):
        """Setup self.logic according to the types of the template and the transition system.
        Other strategies
        - Use the get_logic API to analyze the constructed verification condition (See it relies on several Probes of z3).
        - Use some APIs in pySMT?
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
                self.logic = "UFNRA"  # or NRA?
        elif self.sts.has_int:
            template = self.ct.template_type
            if template == TemplateType.ZONE or template == TemplateType.INTERVAL:
                self.logic = "UFLIA"  # or UFLIA?
            else:
                self.logic = "UFNIA"  # or UFNIA?
        elif self.sts.has_bool:
            self.logic == "UF"
        else:
            raise NotImplementedError

    def dump_constraint(self, g_verifier_args) -> bool:
        """Dumping the verification condition"""
        # global g_verifier_args
        assert g_verifier_args.dump_ef_smt2 or g_verifier_args.dump_qbf
        assert g_verifier_args.dump_ef_smt2 != g_verifier_args.dump_qbf
        qf_vc = self.generate_quantifier_free_vc()
        ef_solver = EFSMTSolver(logic=self.logic, solver=self.solver)
        forall_vars = self.sts.all_variables
        # exists_vars = []

        exists_vars = extract_all(self.ct.template_vars)
        ef_solver.init(exist_vars=exists_vars, forall_vars=forall_vars, phi=qf_vc)

        # TODO: allowing for controlling the output dir
        # g_verifier_args.dump_cnt_dir
        import os
        # file_name = g_verifier_args.file  # the input instance
        # print(g_verifier_args.dump_cnt_dir, os.path.basename(g_verifier_args.file))
        file_name = "{0}/{1}".format(g_verifier_args.dump_cnt_dir, os.path.basename(g_verifier_args.file))
        file_name += "+{}".format(str(g_verifier_args.template))
        file_name += "+d{}".format(str(g_verifier_args.num_disjunctions))
        file_name += "+strength_{}".format(str(g_verifier_args.prop_strengthen))
        file_name += "+ouflow_{}".format(str(g_verifier_args.prevent_over_under_flows))

        if g_verifier_args.dump_ef_smt2:
            file_name += ".smt2"
            print("Dumping SMT constraint to {}".format(file_name))
            ef_solver.dump_ef_smt_file(smt2_file_name=file_name)
        elif g_verifier_args.dump_qbf:
            file_name += ".qdimacs"
            print("Dumping QBF constraint to {}".format(file_name))
            ef_solver.dump_qbf_file(qdimacs_file_name=file_name)
        else:
            raise NotImplementedError

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """The interface for calling different engines"""
        print("Start solving: ")
        print("Used template: {}".format(str(self.ct.template_type)))
        print("Used logic: {}".format(str(self.logic)))
        if self.solver == "z3api":
            # will call z3's Python API to solve the problem (no need to dump files)
            return self.solve_with_z3()
        else:
            # Call third-party solvers via EFSMTSolver
            #   1. Dump to SMT-LIB2 file and call a binary solver (e.g., cvc5, z3..)
            #   2. Translate to various Boolean formats and use corresponding solvers
            #   3. Use PySMT-based implementation of the CEGIS-based solver
            qf_vc = self.generate_quantifier_free_vc()
            print("EFSMT starting!!!")
            ef_solver = EFSMTSolver(logic=self.logic, solver=self.solver, pysmt_solver=self.pysmt_solver)
            forall_vars = self.sts.all_variables
            exists_vars = extract_all(self.ct.template_vars)  # self.ct.template_vars can be a nested list
            # print(self.ct.template_vars)
            # print(exists_vars)
            # exit(0)
            # print("qf part of vc: ", qf_vc)
            # print("exists vars: ", exists_vars)
            # print("forall vars: ", forall_vars)
            ef_solver.init(exist_vars=exists_vars, forall_vars=forall_vars, phi=qf_vc)
            res = ef_solver.solve()
            if res == "sat":
                # Try to extract the model and build an invariant
                model = ef_solver.get_model()
                if model:
                    invariant = self.ct.build_invariant(model)
                    return VerificationResult(True, invariant)
                return VerificationResult(True, None)
            else:
                return VerificationResult(False, None)

    def generate_vc(self) -> z3.ExprRef:
        """ Generate VC (Version 1)
        Another strategy is to generate the quantifier free body first and then add the
        quantifier once (to self.sts.all_variables), which is implemented in generate_vc2
        """
        s = z3.Solver()
        if self.prop_strengthening:
            # Since we use "template = P and template" as the invariant template,
            # we need to adjunct the logic for generating the constraints
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
        # FIXME: this seems to be some "technicla debt" (not sure why we do this)
        #  Indeed, for most domains, get_additional_cnts_for_template_vars() returns true.
        if self.ct.template_type == TemplateType.INTERVAL or \
                self.ct.template_type == TemplateType.DISJUNCTIVE_INTERVAL or \
                self.ct.template_type == TemplateType.ZONE or self.ct.template_type == TemplateType.OCTAGON:
            s.add(self.ct.get_additional_cnts_for_template_vars())

        return z3.And(s.assertions())

    def generate_quantifier_free_vc(self) -> z3.ExprRef:
        """Generate the "QF-part" of the VC (quantifiers will be added later
         by the generate_vc2 function)"""
        s = z3.Solver()
        if self.prop_strengthening:
            # use "template = P and template" as the invariant template!!
            var_map = []  # x' to x, y' to y
            for i in range(len(self.sts.variables)):
                var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            post_in_prime = z3.substitute(self.sts.post, var_map)  # post cond that uses x', y', ..

            s.add(z3.Implies(self.sts.init,
                             z3.And(self.sts.post, self.ct.template_cnt_init_and_post)))
            s.add(z3.Implies(z3.And(self.sts.post, self.ct.template_cnt_init_and_post, self.sts.trans),
                             z3.And(post_in_prime, self.ct.template_cnt_trans)))
            if not self.ignore_post_cond:
                s.add(z3.Implies(z3.And(self.sts.post, self.ct.template_cnt_init_and_post),
                                 self.sts.post))
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
        logger.debug("Finish generating VC")
        return z3.ForAll(self.sts.all_variables, qf_vc)

    def solve_with_z3(self) -> VerificationResult:
        """This is the main entrance for the verification"""
        s = z3.SolverFor(self.logic)
        vc = self.generate_vc2()
        # TODO: use the interface in efsmt/efsmt_solver.py
        #     e.g., pass the following y and phi to EFSMTSolver
        #       y = self.sts.all_variables
        #       phi = self.generate_quantifier_free_vc()
        #     One possible problem is: to build the invariant, we need a model, which
        #     may not be very easy to be parsed if we use a bin solver
        if self.print_vc:
            print(vc)
        s.add(vc)  # sometimes can be much faster!
        print("EFSMT starting (via z3py API)!!!")
        start = time.time()
        # print(s.to_smt2())
        check_res = s.check()
        print("EFSMT time: ", time.time() - start)
        if check_res == z3.sat:
            print("sat")
            model = s.model()
            invariant = self.ct.build_invariant(model)
            return VerificationResult(True, invariant)
        else:
            print("unknown")
            return VerificationResult(False, None)
