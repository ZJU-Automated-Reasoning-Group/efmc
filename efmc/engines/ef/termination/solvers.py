"""
Solvers for termination verification conditions.
"""

import logging
from typing import Optional
import z3

from efmc.engines.ef.efsmt.efsmt_solver import EFSMTSolver
from efmc.utils.z3_expr_utils import extract_all
from .result_types import TerminationResult, NonTerminationResult

logger = logging.getLogger(__name__)


class RankingSolver:
    """Solver for ranking function verification conditions."""
    
    def __init__(self, logic: str = "BV", solver: str = "z3api"):
        self.logic = logic
        self.solver = solver

    def solve(self, vc: z3.ExprRef, template, timeout: Optional[int] = None) -> TerminationResult:
        """Solve the ranking function verification condition."""
        exists_vars = extract_all(template.template_vars)
        if hasattr(template, 'condition_vars'):
            exists_vars.extend(template.condition_vars)
        
        forall_vars = getattr(template, 'sts', None)
        if forall_vars:
            forall_vars = forall_vars.all_variables
        else:
            forall_vars = []
        
        if self.solver == "z3api" and timeout:
            return self._solve_with_timeout(vc, exists_vars, forall_vars, timeout)
        
        try:
            ef_solver = EFSMTSolver(logic=self.logic, solver=self.solver)
            ef_solver.init(exist_vars=exists_vars, forall_vars=forall_vars, phi=vc)
            result = ef_solver.solve()
            
            return TerminationResult(
                result=(result == "sat"),
                error=None if result == "sat" else f"Could not find ranking function: {result}"
            )
        except Exception as e:
            logger.error(f"Error in EF solver: {e}")
            return TerminationResult(result=False, error=f"Solver error: {e}")

    def _solve_with_timeout(self, vc: z3.ExprRef, exists_vars, forall_vars, timeout: int) -> TerminationResult:
        """Solve with Z3 directly using timeout."""
        try:
            solver = z3.Solver()
            solver.set("timeout", timeout * 1000)
            
            formula = z3.ForAll(forall_vars, vc) if forall_vars else vc
            solver.add(formula)
            
            result = solver.check()
            
            if result == z3.sat:
                return TerminationResult(result=True)
            elif result == z3.unsat:
                return TerminationResult(result=False, error="No ranking function exists")
            else:
                return TerminationResult(result=False, error="Solver timeout or unknown result")
                
        except Exception as e:
            logger.error(f"Error in Z3 solver: {e}")
            return TerminationResult(result=False, error=f"Z3 solver error: {e}")


class RecurrenceSolver:
    """Solver for recurrence set verification conditions."""
    
    def __init__(self, logic: str = "BV", solver: str = "z3api"):
        self.logic = logic
        self.solver = solver

    def solve(self, vc: z3.ExprRef, template, timeout: Optional[int] = None) -> NonTerminationResult:
        """Solve the recurrence set verification condition."""
        exists_vars = extract_all(template.template_vars)
        if hasattr(template, 'condition_vars'):
            exists_vars.extend(template.condition_vars)
        
        forall_vars = getattr(template, 'sts', None)
        if forall_vars:
            forall_vars = forall_vars.all_variables
        else:
            forall_vars = []
        
        if self.solver == "z3api" and timeout:
            return self._solve_with_timeout(vc, exists_vars, forall_vars, timeout)
        
        try:
            ef_solver = EFSMTSolver(logic=self.logic, solver=self.solver)
            ef_solver.init(exist_vars=exists_vars, forall_vars=forall_vars, phi=vc)
            result = ef_solver.solve()
            
            return NonTerminationResult(
                result=(result == "sat"),
                error=None if result == "sat" else f"Could not find recurrence set: {result}"
            )
        except Exception as e:
            logger.error(f"Error in EF solver: {e}")
            return NonTerminationResult(result=False, error=f"Solver error: {e}")

    def _solve_with_timeout(self, vc: z3.ExprRef, exists_vars, forall_vars, timeout: int) -> NonTerminationResult:
        """Solve with Z3 directly using timeout."""
        try:
            solver = z3.Solver()
            solver.set("timeout", timeout * 1000)
            
            formula = z3.ForAll(forall_vars, vc) if forall_vars else vc
            solver.add(formula)
            
            result = solver.check()
            
            if result == z3.sat:
                return NonTerminationResult(result=True)
            elif result == z3.unsat:
                return NonTerminationResult(result=False, error="No recurrence set exists")
            else:
                return NonTerminationResult(result=False, error="Solver timeout or unknown result")
                
        except Exception as e:
            logger.error(f"Error in Z3 solver: {e}")
            return NonTerminationResult(result=False, error=f"Z3 solver error: {e}") 