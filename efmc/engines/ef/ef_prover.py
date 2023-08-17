# coding: utf-8
"""
Constraint/template based invariant inference using EFSMT solving
NOTE:
 - We assume there is only one invariant to be synthesized.
 - This file relies heavily on the templates in efmc.templates
"""

import logging
import time
# from enum import Enum

import z3

from efmc.sts import TransitionSystem
from efmc.utils import is_entail
from efmc.engines.ef.templates import *
from efmc.engines.ef.efsmt.efsmt_solver import EFSMTSolver

logger = logging.getLogger(__name__)


def extract_all(lst):
    """extract all elements from nested lists"""
    results = []
    for elem in lst:
        if isinstance(elem, list):
            results.extend(extract_all(elem))
        else:
            results.append(elem)
    return results


class EFProver:
    """
    Exists-Forall SMT Solving for Inductive Invariant Inference
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

    def set_template(self, template_name: str, num_disjunctions=2):
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
                self.logic = "UFNRA"  # or UFNRA?
        elif self.sts.has_int:
            template = self.ct.template_type
            if template == TemplateType.ZONE or template == TemplateType.INTERVAL:
                self.logic = "UFLIA"  # or UFLIA?
            else:
                self.logic = "UFNIA"  # or UFNIA?
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

    def dump_constraint(self, g_verifier_args) -> bool:
        """Dumping the verification condition"""
        # global g_verifier_args
        assert g_verifier_args.dump_ef_smt2 or g_verifier_args.dump_qbf
        assert g_verifier_args.dump_ef_smt2 != g_verifier_args.dump_qbf
        qf_vc = self.generate_quantifier_free_vc()
        ef_solver = EFSMTSolver(logic=self.logic, solver=self.solver)
        forall_vars = self.sts.all_variables
        # exists_vars = []
        # for ele in self.ct.template_vars:
        #    if isinstance(ele, list):
        #        for v in ele: exists_vars.append(v)
        #    else:
        #        exists_vars.append(ele)
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

    def solve(self) -> bool:
        """The interface for calling different engines"""
        print("Start solving: ")
        print("Used template: {}".format(str(self.ct.template_type)))
        print("Used logic: {}".format(str(self.logic)))
        # return self.solve_with_cegis_efsmt()  # FIXME: seems very slow
        if self.solver == "z3api":
            return self.solve_with_z3()
        else:
            # call third-party solvers via EFSMTSolver
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
            return res
            # print("res..", res)

    def generate_vc(self) -> z3.ExprRef:
        """ Generate VC (Version 1)
        Another strategy is to generate the quantifier free body first and then add the
        quantifier once (to self.sts.all_variables), which is implemented in generate_vc2
        """
        s = z3.Solver()
        if self.prop_strengthening:
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
        # Add additional cnts to restrict the template variables
        # if self.ct.template_type != TemplateType.POLYHEDRON:
        #    qf_vc = z3.And(qf_vc, self.ct.get_additional_cnts_for_template_vars())
        # qf_vc = ctx_simplify(qf_vc) # can be slow
        logger.debug("Finish generating VC")
        return z3.ForAll(self.sts.all_variables, qf_vc)

    def solve_with_z3(self) -> str:
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
        if check_res == z3.sat:
            print("EFSMT success time: ", time.time() - start)
            m = s.model()
            if self.prop_strengthening:
                # use "template = P and template" as the invariant template
                inv = z3.And(self.sts.post, self.ct.build_invariant_expr(m, use_prime_variables=False))
                print("Invariant: ", inv)
                if self.validate_invariant:
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
                if self.validate_invariant:
                    inv_in_prime_variables = self.ct.build_invariant_expr(m, use_prime_variables=True)
                    self.check_invariant(inv, inv_in_prime_variables)
            self.inductive_invaraint = inv  # preserve the invariant
            return "sat"
        else:
            print("EFSMT fail time: ", time.time() - start)
            print("Cannot verify using the template!")
            print(check_res)
            if check_res == z3.unknown:
                print(s.reason_unknown())
            return "unsat"
