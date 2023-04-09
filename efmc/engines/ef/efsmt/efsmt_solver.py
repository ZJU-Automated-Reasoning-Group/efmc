# coding: utf-8
"""
The uniformed interface for solving Exists-ForAll problems
"""
import logging
from enum import Enum
from typing import List

import z3

from efmc.engines.ef.efsmt.efsmt_utils import solve_with_bin_smt, solve_with_bin_qbf
from efmc.engines.ef.efsmt.efbv_to_bool import EFBVFormulaTranslator

logger = logging.getLogger(__name__)


def simple_cegis_efsmt(logic: str, x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, maxloops=None, profiling=False):
    """ Solves exists x. forall y. phi(x, y) with simple CEGIS
    """
    # x = [item for item in get_vars(phi) if item not in y]
    # set_param("verbose", 15); set_param("smt.arith.solver", 3)
    if "IA" in logic:
        qf_logic = "QF_LIA"
    elif "RA" in logic:
        qf_logic = "QF_LRA"
    elif "BV" in logic:
        qf_logic = "QF_BV"
    else:
        qf_logic = ""

    if qf_logic != "":
        esolver = z3.SolverFor(qf_logic)
        fsolver = z3.SolverFor(qf_logic)
    else:
        esolver = z3.Solver()
        fsolver = z3.Solver()

    e_solver_cnts = []  # storing all the queries for profiling
    f_solver_cnts = []  # storing all the queries for profiling
    if profiling:
        e_solver_cnts.append("(set-logic {})".format(qf_logic))
        f_solver_cnts.append("(set-logic {})".format(qf_logic))
        for var in x:
            e_solver_cnts.append("(declare-const {0} {1})".format(var.sexpr(), var.sort().sexpr()))
        for var in y:
            f_solver_cnts.append("(declare-const {0} {1})".format(var.sexpr(), var.sort().sexpr()))

    esolver.add(z3.BoolVal(True))

    loops = 0
    res = z3.unknown
    while maxloops is None or loops <= maxloops:
        loops += 1
        # print("round: ", loops)
        eres = esolver.check()

        if profiling and loops >= 2:
            e_solver_cnts.append("(check-sat)")

        if eres == z3.unsat:
            res = z3.unsat
            break
        else:
            emodel = esolver.model()
            mappings = [(var, emodel.eval(var, model_completion=True)) for var in x]
            sub_phi = z3.simplify(z3.substitute(phi, mappings))
            fsolver.push()
            fsolver.add(z3.Not(sub_phi))

            if profiling:
                f_solver_cnts.append("(push)")
                f_solver_cnts.append("(assert {})".format(z3.Not(sub_phi).sexpr()))
                f_solver_cnts.append("(check-sat)")

            if fsolver.check() == z3.sat:
                fmodel = fsolver.model()
                y_mappings = [(var, fmodel.eval(var, model_completion=True)) for var in y]
                sub_phi = z3.simplify(z3.substitute(phi, y_mappings))
                esolver.add(sub_phi)
                fsolver.pop()
                if profiling:
                    e_solver_cnts.append("(assert {})".format(sub_phi.sexpr()))
                    f_solver_cnts.append("(pop)")
            else:
                res = z3.sat
                break
    # if profiling:
    #    print(e_solver_cnts)
    #    print(f_solver_cnts)
    return res


def solve_z3qbf(fml: z3.ExprRef):
    """Solve Exists X Forall Y Exists Z . P(...), which is translated from an exists-forall bit-vector instance
    NOTE: We do not need to explicitly specify the first Exists
    Z: the aux Boolean vars (e.g., introduced by the bit-blasting and CNF transformer?)
    """
    logger.debug("Solving QBF via Z3")
    sol = z3.Solver()
    sol.add(fml)
    res = sol.check()
    return res


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

    def set_tactic(self, name: str):
        raise NotImplementedError

    def init(self, exist_vars, forall_vars, phi: z3.ExprRef):
        self.exists_vars = exist_vars
        self.forall_vars = forall_vars
        self.phi = phi
        self.initialized = True

    def dump_cegis_smt_files(self):
        print("Profiling the simple, sequential, CEGIS-style EFSMT!")
        simple_cegis_efsmt(self.logic, self.exists_vars, self.forall_vars, self.phi, profiling=True)

    def dump_ef_smt_file(self, smt2_file_name: str):
        """Dump the constraint from the ef engine
        """
        fml_str = "(set-logic {})\n".format(self.logic)
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
        logger.debug("EFSMT solver: {}".format(self.solver))
        if self.solver == "z3":
            return solve_with_bin_smt(self.logic, self.forall_vars, self.phi, "z3")
        elif self.solver == "cvc5":
            return solve_with_bin_smt(self.logic, self.forall_vars, self.phi, "cvc5")
        elif self.solver == "btor":
            return solve_with_bin_smt(self.logic, self.forall_vars, self.phi, "boolector2")
        elif self.solver == "yices2":
            return solve_with_bin_smt(self.logic, self.forall_vars, self.phi, "yices2")
        elif self.solver == "cegis":
            # FIXME: the following code uses Z3's API. Should we support other engines?
            return self.solve_with_simple_cegis()
        elif self.solver == "z3qbf":
            return self.solve_with_z3_qbf()
        elif self.solver == "caqe":
            # return self.solve_with_z3_qbf()
            return self.solve_with_third_party_qbf("caqe")
        else:
            raise NotImplementedError

    def solve_with_simple_cegis(self):
        """Solve with a CEGIS-style algorithm, which consists of a "forall solver" and an "exists solver"
        """
        """This can be slow (perhaps not a good idea for NRA) Maybe good for LRA or BV?"""
        print("Simple, sequential, CEGIS-style EFSMT!")
        z3_res = simple_cegis_efsmt(self.logic, self.exists_vars, self.forall_vars, self.phi)
        return z3_res

    def solve_with_z3_qbf(self):
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        return solve_z3qbf(fml_manager.to_z3_qbf(self.phi, self.exists_vars, self.forall_vars))

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
    solver.dump_cegis_smt_files()
    print("time: ", time.time() - start)


if __name__ == '__main__':
    demo_efsmt()
