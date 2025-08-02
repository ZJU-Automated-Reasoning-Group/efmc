"""
Farkas-based invariant inference prover.
"""
import logging
import time
from typing import Optional

import z3

from efmc.sts import TransitionSystem
from efmc.engines.ef.farkas.farkas_template import FarkasTemplate
from efmc.utils.verification_utils import VerificationResult, check_invariant

logger = logging.getLogger(__name__)


class FarkasProver:
    """
    Farkas-based invariant inference prover using linear templates.
    
    Synthesizes linear invariants by:
    1. Creating linear templates with unknown coefficients
    2. Applying Farkas' Lemma to eliminate universal quantifiers
    3. Solving the constraint system to find invariant coefficients
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        self.num_templates = kwargs.get("num_templates", 3)
        self.solver_name = kwargs.get("solver", "z3api")
        self.validate_invariant = kwargs.get("validate_invariant", True)
        self.timeout = kwargs.get("timeout", None)
        self.verbose = kwargs.get("verbose", False)
        
        if self.sts.has_bv:
            logger.warning("Farkas prover does not support bit-vector relations.")
        
        self.template = None
        self.invariant = None
        self.solve_time = 0

    def _create_template(self) -> FarkasTemplate:
        """Create Farkas template for the transition system."""
        return FarkasTemplate(self.sts, num_templates=self.num_templates)

    def _setup_solver(self) -> z3.Solver:
        """Set up Z3 solver with appropriate logic and timeout."""
        if self.sts.has_real:
            solver = z3.SolverFor("QF_NRA")
        elif self.sts.has_int:
            solver = z3.SolverFor("QF_NIA")
        else:
            solver = z3.Solver()
        
        if self.timeout:
            solver.set("timeout", self.timeout * 1000)
        
        return solver

    def _solve_template_constraints(self) -> Optional[z3.ModelRef]:
        """Solve template constraints to find invariant coefficients."""
        solver = self._setup_solver()
        solver.add(self.template.template_cnt_init_and_post)
        solver.add(self.template.template_cnt_trans)
        
        if self.verbose:
            logger.info("Solving Farkas template constraints...")
        
        result = solver.check()
        return solver.model() if result == z3.sat else None

    def _validate_synthesized_invariant(self, invariant: z3.ExprRef) -> bool:
        """Validate the synthesized invariant."""
        if not self.validate_invariant:
            return True
        
        invariant_prime = z3.substitute(
            invariant, list(zip(self.sts.variables, self.sts.prime_variables))
        )
        return check_invariant(self.sts, invariant, invariant_prime)

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """Solve using Farkas-based invariant synthesis."""
        if timeout:
            self.timeout = timeout
        
        start_time = time.time()
        
        try:
            if self.verbose:
                logger.info(f"Starting Farkas synthesis with {self.num_templates} templates")
            
            self.template = self._create_template()
            model = self._solve_template_constraints()
            self.solve_time = time.time() - start_time
            
            if not model:
                if self.verbose:
                    logger.info(f"Farkas synthesis failed after {self.solve_time:.2f}s")
                return VerificationResult(is_safe=False, invariant=None, is_unknown=True)
            
            invariant = self.template.build_invariant_expr(model)
            
            if self.verbose:
                logger.info(f"Synthesized invariant: {invariant}")
            
            if self.validate_invariant and not self._validate_synthesized_invariant(invariant):
                logger.error("Synthesized invariant failed validation")
                return VerificationResult(is_safe=False, invariant=None, is_unknown=True)
            
            self.invariant = invariant
            
            if self.verbose:
                logger.info(f"Farkas synthesis successful in {self.solve_time:.2f}s")
            
            return VerificationResult(is_safe=True, invariant=invariant)
            
        except Exception as e:
            self.solve_time = time.time() - start_time
            logger.error(f"Farkas synthesis error: {e}")
            return VerificationResult(is_safe=False, invariant=None, is_unknown=True)

    def reset(self):
        """Reset prover state."""
        self.template = None
        self.invariant = None
        self.solve_time = 0

    def get_statistics(self) -> dict:
        """Get solving statistics."""
        return {
            "solve_time": self.solve_time,
            "num_templates": self.num_templates,
            "has_invariant": self.invariant is not None,
            "solver": self.solver_name
        }

    def __str__(self) -> str:
        return f"FarkasProver(templates={self.num_templates}, solver={self.solver_name})"
