# coding: utf-8
"""
The uniformed interface for solving Exists-ForAll problems
"""
import logging
# from enum import Enum
from typing import List

import z3

from efmc.engines.ef.efsmt.efsmt_bin_solvers import solve_with_bin_smt, solve_with_bin_qbf
from efmc.engines.ef.efsmt.efsmt_cegis_solvers import simple_cegis_efsmt
from efmc.engines.ef.efsmt.efbv_to_bool import EFBVFormulaTranslator

logger = logging.getLogger(__name__)


class EFSMTSolver:
    """Solving exists forall problem"""

    def __init__(self, logic: str, **kwargs):
        self.phi = None
        self.exists_vars = None
        self.forall_vars = None

        self.logic = logic

        self.seed = kwargs.get("seed", 1)  # random seed
        self.solver = kwargs.get("solver", "z3")

        self.initialized = False
        self.pysmt_solver = kwargs.get("pysmt_solver", "z3")

    def set_tactic(self, name: str):
        raise NotImplementedError

    def init(self, exist_vars, forall_vars, phi: z3.ExprRef):
        self.exists_vars = exist_vars
        self.forall_vars = forall_vars
        self.phi = phi
        self.initialized = True

    def dump_ef_smt_file(self, smt2_file_name: str):
        """Dump the constraint from the ef engine
        """
        fml_str = "(set-logic {})\n".format(self.logic)

        dump_strategy = 1
        if dump_strategy == 1:

            # there are duplicates in self.exists_vars???
            exits_vars_names = set()
            for v in self.exists_vars:
                name = str(v)
                if name not in exits_vars_names:
                    exits_vars_names.add(name)
                    fml_str += "(declare-const {0} {1})\n".format(v.sexpr(), v.sort().sexpr())

            quant_vars = "("
            for v in self.forall_vars:
                quant_vars += "({0} {1}) ".format(v.sexpr(), v.sort().sexpr())
            quant_vars += ")\n"

            quant_fml_body = "(and \n"
            s = z3.Solver()
            s.add(self.phi)
            # self.phi is in the form of
            #  and (Init, Trans, Post)
            assert (z3.is_app(self.phi))
            for fml in self.phi.children():
                quant_fml_body += "  {}\n".format(fml.sexpr())
            quant_fml_body += ")"

            fml_body = "(assert (forall {0} {1}))\n".format(quant_vars, quant_fml_body)
            fml_str += fml_body
            fml_str += "(check-sat)\n"
        else:
            # Another more direct strategy
            # But we cannot see the definition of the VC clearly
            sol = z3.Solver()
            sol.add(z3.ForAll(self.forall_vars, self.phi))
            fml_str += sol.to_smt2()

        tmp = open(smt2_file_name, "w")
        tmp.write(fml_str)
        tmp.close()

    def dump_qbf_file(self, qdimacs_file_name: str):
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        qdimacs_str = fml_manager.to_qdimacs_str(self.phi, existential_vars=self.exists_vars,
                                                 universal_vars=self.forall_vars)
        tmp = open(qdimacs_file_name, "w")
        tmp.write(qdimacs_str)
        tmp.close()

    def dump_sat_file(self, dimacs_file_name: str):
        raise NotImplementedError

    def solve(self):
        """Translate EFSMT(BV) to QBF (preserve the quantifiers)
        """
        assert self.initialized
        print("EFSMT solver: {}".format(self.solver))
        # 1. Quantifier instantiation
        if self.solver == "z3":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "z3")
        elif self.solver == "cvc5":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "cvc5")
        elif self.solver == "btor":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "boolector2")
        # TODO: Bitzullia (new solver)
        elif self.solver == "yices2":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "yices2")
        elif self.solver == "mathsat":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "mathsat")
        elif self.solver == "bitwuzla":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "bitwuzla")
        
        # 2. Bit-blasting
        elif self.solver == "z3qbf":
            return self.solve_with_z3_qbf()
        elif self.solver == "caqe":
            return self.solve_with_third_party_qbf("caqe")
        # TODO: q3b (BDD-based), z3-based QE+SAT
        elif self.solver == "q3b":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "q3b")
        
        # 3. Simple cegis-based
        elif self.solver == "cegis":
            # TODO: other engines in pysmt
            print("solving via cegis_solver")
            return self.solve_with_simple_cegis()

        else:
            raise NotImplementedError

    def solve_with_simple_cegis(self):
        """Solve with a CEGIS-style algorithm, which consists of a "forall solver" and an "exists solver"

        This can be slow (perhaps not a good idea for NRA) Maybe good for LRA or BV?
        """
        print("Simple, sequential, CEGIS-style EFSMT!")
        z3_res = simple_cegis_efsmt(self.logic, self.exists_vars, self.forall_vars, self.phi, pysmt_solver=self.pysmt_solver)
        return z3_res

    def solve_with_z3_qbf(self):
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        sol = z3.Solver()
        vc = fml_manager.to_z3_qbf(self.phi, self.exists_vars, self.forall_vars)
        sol.add(vc)
        res = sol.check()
        return res

    def solve_with_z3_sat(self, y: List[z3.ExprRef], phi: z3.ExprRef):
        raise NotImplementedError

    def solve_with_third_party_qbf(self, solver_name: str):
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        qdimacs = fml_manager.to_qdimacs_str(self.phi, existential_vars=self.exists_vars,
                                             universal_vars=self.forall_vars)
        return solve_with_bin_qbf(qdimacs, solver_name)

    def solve_with_third_party_sat(self, y: List[z3.ExprRef], phi: z3.ExprRef):
        """
        Use third-party SAT solvers... (do we need?)
        """
        raise NotImplementedError


def demo_efsmt():
    import time
    x, y, z = z3.BitVecs("x y z", 16)
    # x, y, z = z3.Reals("x y z")
    fmla = z3.Implies(z3.And(y > 0, y < 10), y - 2 * x < 7)

    start = time.time()
    solver = EFSMTSolver(logic="BV", solver="cegis")
    solver.init(exist_vars=[x], forall_vars=[y], phi=fmla)
    # solver.dump_cegis_smt_files()
    print("time: ", time.time() - start)


if __name__ == '__main__':
    demo_efsmt()
