# coding: utf-8
"""
The uniformed interface for solving Exists-ForAll problems
"""
import logging
from enum import Enum
from typing import List

import z3

from efmc.engines.ef.efsmt.efsmt_utils import solve_with_bin_smt
from efmc.engines.ef.efsmt.efbv_formula_manager import EFBVFormulaTranslator

logger = logging.getLogger(__name__)


class EFSMTStrategy(Enum):
    Z3 = 0,  # via API
    CVC5 = 1,  # via bin solver
    Boolector = 2,  # via bin solver
    Yices2 = 3,  # via bin solver
    SIMPLE_CEGAR = 4,
    QBF = 5,
    SAT = 6


def simple_cegar_efsmt(logic: str,  x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, maxloops=None):
    """ Solves exists x. forall y. phi(x, y) with simple CEGAR
    """
    # x = [item for item in get_vars(phi) if item not in y]
    # set_param("verbose", 15)
    # set_param("smt.arith.solver", 3)
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

    esolver.add(z3.BoolVal(True))

    loops = 0
    while maxloops is None or loops <= maxloops:
        loops += 1
        # print("round: ", loops)
        eres = esolver.check()
        if eres == z3.unsat:
            return z3.unsat
        else:
            emodel = esolver.model()
            mappings = [(var, emodel.eval(var, model_completion=True)) for var in x]
            sub_phi = z3.simplify(z3.substitute(phi, mappings))
            fsolver.push()
            fsolver.add(z3.Not(sub_phi))
            if fsolver.check() == z3.sat:
                fmodel = fsolver.model()
                y_mappings = [(var, fmodel.eval(var, model_completion=True)) for var in y]
                sub_phi = z3.simplify(z3.substitute(phi, y_mappings))
                esolver.add(sub_phi)
                fsolver.pop()
            else:
                return z3.sat
    return z3.unknown


def solve_with_z3(logic: str, y: List[z3.ExprRef], phi: z3.ExprRef) -> z3.CheckSatResult:
    """Call Z3's Python API"""
    qfml = z3.ForAll(y, phi)
    s = z3.SolverFor(logic)  # can be very fast
    s.add(qfml)
    return s.check()


def solve_qbf(fml: z3.ExprRef):
    """Solve Exists X Forall Y Exists Z . P(...), which is translated from an exists-forall bit-vector instance
    NOTE: We do not need to explicitly specify the first Exists
    Z: the aux Boolean vars (e.g., introduced by the bit-blasting and CNF transformer?)
    """
    sol = z3.Solver()
    sol.add(fml)
    res = sol.check()
    return res


class EFSMTSolver:
    """Solving exists forall problem"""

    def __init__(self, logic: str):
        self.phi = None
        self.exists_vars = None
        self.forall_vars = None
        self.tactic = EFSMTStrategy.Z3
        self.logic = logic

    def set_tactic(self, name: str):
        raise NotImplementedError

    def init_instances(self, exist_vars, forall_vars, phi: z3.ExprRef):
        self.exists_vars = exist_vars
        self.forall_vars = forall_vars
        self.phi = phi

    def solve(self):
        """Translate EFSMT(BV) to QBF (preserve the quantifiers)
        """
        if self.tactic == EFSMTStrategy.Z3 or self.tactic == EFSMTStrategy.CVC5 \
                or self.tactic == EFSMTStrategy.Boolector or self.tactic == EFSMTStrategy.Yices2:
            return self.solve_with_qsmt()
        elif self.tactic == EFSMTStrategy.SIMPLE_CEGAR:
            return self.solve_with_simple_cegar()
        elif self.tactic == EFSMTStrategy.QBF:
            return self.solve_with_qbf()
        else:
            raise NotImplementedError

    def solve_with_simple_cegar(self):
        """Solve with a CEGAR-style algorithm, which consists of a "forall solver" and an "exists solver"
        """
        """This can be slow (perhaps not a good idea for NRA) Maybe good for LRA or BV?"""
        print("Simple, sequential, CEGAR-style EFSMT!")
        z3_res, model = simple_cegar_efsmt(self.logic, self.exists_vars, self.forall_vars, self.phi)
        return z3_res, model

    def solve_with_qsmt(self) -> z3.CheckSatResult:
        """Solve with bin solvers"""
        if self.tactic == EFSMTStrategy.Z3:
            return solve_with_z3(self.logic, self.forall_vars, self.phi)
            # return solve_with_bin_smt(y, phi, self.logic, "z3")
        elif self.tactic == EFSMTStrategy.CVC5:
            return solve_with_bin_smt(self.logic, self.forall_vars, self.phi, "cvc5")
        elif self.tactic == EFSMTStrategy.Boolector:
            return solve_with_bin_smt(self.logic, self.forall_vars, self.phi, "boolector2")
        elif self.tactic == EFSMTStrategy.Yices2:
            return solve_with_bin_smt(self.logic, self.forall_vars, self.phi, "yices2")
        else:
            raise NotImplementedError

    def solve_with_qbf(self):
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        return solve_qbf(fml_manager.to_qbf(self.phi, self.exists_vars, self.forall_vars))

    def solve_with_sat(self, y: List[z3.ExprRef], phi: z3.ExprRef):
        raise NotImplementedError
