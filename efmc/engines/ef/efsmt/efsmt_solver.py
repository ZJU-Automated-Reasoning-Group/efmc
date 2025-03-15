# coding: utf-8
"""
The uniformed interface for solving Exists-ForAll problems over bit-vectors.

Solver options:
- "z3": Use Z3 SMT solver
- "cvc5": Use CVC5 SMT solver
- "btor": Use Boolector SMT solver
- "bitwuzla": Use Bitwuzla SMT solver
- "yices": Use Yices SMT solver
- "mathsat": Use MathSAT SMT solver
- "q3b": Use Q3B solver
- "caqe": Use CAQE QBF solver
- "cegis": Use CEGIS-based approach
- "sat": Use SAT-based approach
- ...?

Approaches:
- 1. Quantifier instantiation: Direct solving with SMT solvers that support quantifiers
- 2. Bit-blasting: Translation to QBF, BDD, or SAT, and solving with QBF solvers, BDD solvers, or SAT solvers
- 3. CEGIS: CEGIS-based iterative approach (using a SMT oracle for deciding quantifier-free formulas)
"""

import logging
# from enum import Enum
# from typing import List

import z3

from efmc.engines.ef.efsmt.efsmt_bin_solvers import solve_with_bin_smt, solve_with_bin_qbf
from efmc.engines.ef.efsmt.efsmt_cegis_solvers import simple_cegis_efsmt
from efmc.engines.ef.efsmt.efbv_to_bool import EFBVFormulaTranslator
from efmc.engines.ef.efsmt.efsmt_sat_solver import solve_with_sat_solver

logger = logging.getLogger(__name__)


class EFSMTSolver:
    """Solving exists forall problem over bit-vectors."""

    def __init__(self, logic: str, **kwargs):
        self.phi = None
        self.exists_vars = None
        self.forall_vars = None

        self.logic = logic

        self.seed = kwargs.get("seed", 1)  # random seed
        # the solver for solving the EF problem
        self.solver = kwargs.get("solver", "z3")

        self.initialized = False
        # the pysmt library allows for using different SMT solvers
        # NOTE: it seems that only z3 is installed automatically when we install pysmt
        # For other SMT solvers, we need to use the pysmt-install command to install
        self.pysmt_solver = kwargs.get("pysmt_solver", "z3")

    def set_tactic(self, name: str):
        raise NotImplementedError

    def init(self, exist_vars, forall_vars, phi: z3.ExprRef):
        """Initialize the solver"""
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
        """Dump to QBF formula"""
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        qdimacs_str = fml_manager.to_qdimacs_str(self.phi, existential_vars=self.exists_vars,
                                                 universal_vars=self.forall_vars)
        tmp = open(qdimacs_file_name, "w")
        tmp.write(qdimacs_str)
        tmp.close()

    def dump_cnf_file(self, dimacs_file_name: str):
        """Dump to CNF formula"""
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        # FIXME: to_cnf_str() is not implemented
        cnf_str = fml_manager.to_cnf_str(self.phi, existential_vars=self.exists_vars,
                                         universal_vars=self.forall_vars)
        tmp = open(dimacs_file_name, "w")
        tmp.write(cnf_str)
        tmp.close()

    def solve(self):
        """
        Solve EFSMT(BV) formulas via different strategies
        """
        assert self.initialized
        print("EFSMT solver: {}".format(self.solver))
        # 1. Quantifier instantiation approach
        if self.solver == "z3api":
            # Use z3's Python API to solve the problem
            return self.solve_with_z3_api()
        elif self.solver == "z3":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "z3")
        elif self.solver == "cvc5":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "cvc5")
        elif self.solver == "btor":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "boolector2")
        elif self.solver == "yices2":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "yices2")
        elif self.solver == "mathsat":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "mathsat")
        elif self.solver == "bitwuzla":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "bitwuzla")

        # 2. Bit-blasting approach
        elif self.solver == "z3qbf":
            return self.solve_with_z3_qbf()
        elif self.solver == "caqe":
            return self.solve_with_third_party_qbf("caqe")
        # TODO: q3b (BDD-based), z3-based QE+SAT
        elif self.solver == "q3b":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "q3b")
        elif self.solver == "z3sat":
            return self.solve_with_z3_sat()
        # third-party SAT solves (using pySAT)
        elif self.solver in ['cd', 'cd15', 'gc3', 'gc4', 'g3',
                             'g4', 'lgl', 'mcb', 'mpl', 'mg3',
                             'mc', 'm22', 'mgh']:
            return self.solve_with_third_party_sat(solver_name=self.solver)

        # 3. Simple cegis-based approach
        elif self.solver == "cegis":
            print("solving via cegis_solver")
            return self.solve_with_simple_cegis()

        else:
            raise NotImplementedError

    def solve_with_z3_api(self) -> str:
        """
        Solve Exists-Forall SMT problems directly using Z3's Python API.
        
        This method creates a Z3 solver instance and adds the quantified formula
        that represents the Exists-Forall problem. It then checks satisfiability
        and returns the result as a string.
        
        Returns:
            str: "sat" if the formula is satisfiable, "unsat" if unsatisfiable,
                 or "unknown" if Z3 cannot determine satisfiability.
        """
        print("Solving with Z3 API directly")

        # Create a solver instance
        solver = z3.Solver()

        # Create quantified formula: Exists e. Forall f. phi(e, f)
        # First, convert lists to tuples for Z3 quantifiers
        # exists_vars_tuple = tuple(self.exists_vars)
        forall_vars_tuple = tuple(self.forall_vars)

        # Create the quantified formula
        # quantified_formula = z3.Exists(exists_vars_tuple, 
        #                              z3.ForAll(forall_vars_tuple, self.phi))
        quantified_formula = z3.ForAll(forall_vars_tuple, self.phi)

        # Add the formula to the solver
        solver.add(quantified_formula)

        # Check satisfiability
        result = solver.check()

        # Return result as string
        if result == z3.sat:
            return "sat"
        elif result == z3.unsat:
            return "unsat"
        else:
            return "unknown"

    def solve_with_simple_cegis(self) -> str:
        """Solve with a CEGIS-style algorithm, which consists of a "forall solver" and an "exists solver"
        This can be slow (perhaps not a good idea for NRA) Maybe good for LRA or BV?
        NOTE: Currently, we use pySMT for the implementation
        """
        print("Simple, sequential, CEGIS-style EFSMT!")
        z3_res = simple_cegis_efsmt(self.logic, self.exists_vars, self.forall_vars, self.phi,
                                    pysmt_solver=self.pysmt_solver)
        return z3_res

    def solve_with_z3_qbf(self) -> str:
        """Translate to QBF"""
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        sol = z3.Solver()
        vc = fml_manager.to_z3_qbf(self.phi, self.exists_vars, self.forall_vars)
        sol.add(vc)
        res = sol.check()
        if res == z3.sat:
            return "sat"
        elif res == z3.unsat:
            return "unsat"
        else:
            return "unknown"

    def solve_with_z3_sat(self):
        """Quantifier elimination + SAT solving"""
        assert self.logic == "BV" or self.logic == "UFBV"
        print("Quantifier elimination + SAT solving")
        fml_manager = EFBVFormulaTranslator()
        sol = z3.Solver()
        vc = fml_manager.to_z3_sat(self.phi, self.exists_vars, self.forall_vars)
        # print(vc)
        sol.add(vc)
        res = sol.check()
        if res == z3.sat:
            return "sat"
        elif res == z3.unsat:
            return "unsat"
        else:
            return "unknown"

    def solve_with_third_party_qbf(self, solver_name: str) -> str:
        """Translate EFSMT(BV) to QBF, and call a third-party QBF solver"""
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        qdimacs = fml_manager.to_qdimacs_str(self.phi, existential_vars=self.exists_vars,
                                             universal_vars=self.forall_vars)
        return solve_with_bin_qbf(qdimacs, solver_name)

    def solve_with_third_party_sat(self, solver_name: str) -> str:
        """
        Translate EFSMT(BV) to SAT, and call a third-party SAT solver

        cd(cadical103), cd15(cadical153),
        gc3(gluecard3), gc4(glucard4), g3(glucose3), g4(glucose4),
        lgl(lingeling), mcb(maplechrono), mcm(maplecm), mpl(maplesat)
        mg3(mergesat3), mc(minicard), m22(minisat22, mgh(minsatgh)
        sat_solvers_in_pysat = ['cd', 'cd15', 'gc3', 'gc4', 'g3',
                        'g4', 'lgl', 'mcb', 'mpl', 'mg3',
                        'mc', 'm22', 'mgh']
        """
        assert self.logic == "BV" or self.logic == "UFBV"
        print("Quantifier elimination + SAT solving")
        fml_manager = EFBVFormulaTranslator()
        vc = fml_manager.to_dimacs_str(self.phi, self.exists_vars, self.forall_vars)
        res = solve_with_sat_solver(vc, solver_name=solver_name)
        return res


def demo_efsmt():
    import time
    x, y, z = z3.BitVecs("x y z", 16)
    # x, y, z = z3.Reals("x y z")
    fmla = z3.Implies(z3.And(y > 0, y < 10), y - 2 * x < 7)

    start = time.time()
    solver = EFSMTSolver(logic="BV", solver="cegis")
    solver.init(exist_vars=[x], forall_vars=[y], phi=fmla)
    # solver.dump_cegis_smt_files()
    # print(solver.solve_with_z3_sat())
    print(solver.solve_with_third_party_sat(solver_name="cd"))
    print("time: ", time.time() - start)


if __name__ == '__main__':
    demo_efsmt()
