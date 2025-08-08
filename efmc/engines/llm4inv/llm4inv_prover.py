"""
LLM4Inv Prover (simple guess-and-check)

This version implements a minimal loop:
- Ask the LLM for concrete (hole-free) invariant candidates
- Parse each candidate to a Z3 formula
- Check inductiveness/safety via check_invariant
- Return the first valid invariant
"""

import logging
import time
from typing import Optional, Dict, Any, List

import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult, check_invariant
from .llm_interface import LLMInterface

logger = logging.getLogger(__name__)


class LLM4InvProver:
    """Minimal LLM4Inv prover implementing a simple guess-and-check loop."""

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts

        # Core configuration
        self.timeout = kwargs.get('timeout', 600)
        self.max_iterations = kwargs.get('max_iterations', 10)
        self.bit_width = kwargs.get('bit_width', 32)
        self.llm_model = kwargs.get('llm_model', 'deepseek-v3')
        self.max_candidates_per_iter = kwargs.get('max_candidates_per_iter', 5)

        # Initialize components
        self.llm_interface = LLMInterface(sts, model_name=self.llm_model, bit_width=self.bit_width)

        # Statistics
        self.solve_time = 0.0
        self.result: Optional[VerificationResult] = None
        self.tried_candidates: List[str] = []
    
    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        if timeout is not None:
            self.timeout = timeout

        start_time = time.time()

        logger.info("Starting LLM4Inv guess-and-check synthesis")
        program_description = self._generate_program_description()

        deadline = start_time + self.timeout
        failures_for_feedback: List[str] = []

        try:
            for iteration in range(self.max_iterations):
                if time.time() > deadline:
                    logger.warning("LLM4Inv: timeout reached")
                    break

                logger.info(f"Iteration {iteration + 1}/{self.max_iterations}")

                candidates = self.llm_interface.generate_concrete_invariants(
                    program_code=program_description,
                    failed_candidates=failures_for_feedback,
                    max_candidates=self.max_candidates_per_iter,
                )

                if not candidates:
                    logger.info("No candidates generated; stopping.")
                    break

                for cand_str, cand_expr in candidates:
                    if time.time() > deadline:
                        logger.warning("LLM4Inv: timeout reached during candidate checking")
                        break

                    self.tried_candidates.append(cand_str)
                    logger.debug(f"Checking candidate: {cand_str}")

                    inv = cand_expr
                    var_map = [
                        (var, prime_var)
                        for var, prime_var in zip(self.sts.variables, self.sts.prime_variables)
                    ]
                    inv_prime = z3.substitute(inv, var_map)

                    if check_invariant(self.sts, inv, inv_prime):
                        self.solve_time = time.time() - start_time
                        logger.info(
                            f"LLM4Inv synthesis successful in {self.solve_time:.2f}s after {iteration + 1} iterations"
                        )
                        self.result = VerificationResult(True, inv)
                        return self.result

                    failures_for_feedback.append(cand_str)

            self.solve_time = time.time() - start_time
            logger.info(
                f"LLM4Inv synthesis failed after {self.solve_time:.2f}s and {self.max_iterations} iterations"
            )
            self.result = VerificationResult(False, None)
            return self.result

        except Exception as e:
            logger.error(f"LLM4Inv synthesis error: {e}")
            self.solve_time = time.time() - start_time
            self.result = VerificationResult(False, None)
            return self.result
    
    def _generate_program_description(self) -> str:
        """Generate program description for LLM"""
        description = []
        
        # Add variable information
        variables = [str(v) for v in self.sts.variables]
        description.append(f"Variables: {', '.join(variables)}")
        
        # Add bit width information
        description.append(f"Bit width: {self.bit_width}")
        
        # Add basic transition system information
        description.append("Program behavior:")
        description.append("- Initial condition defines starting states")
        description.append("- Transition relation defines state changes")
        description.append("- Safety property must hold in all reachable states")
        
        return "\n".join(description)
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get comprehensive prover statistics"""
        stats = {
            'solve_time': self.solve_time,
            'timeout': self.timeout,
            'max_iterations': self.max_iterations,
            'bit_width': self.bit_width,
            'llm_model': self.llm_model,
            'success': self.result.is_safe if self.result else False,
            'tried_candidates': len(self.tried_candidates)
        }
        
        # Add LLM interface statistics
        if hasattr(self.llm_interface, 'get_statistics'):
            stats['llm_stats'] = self.llm_interface.get_statistics()
        
        return stats

    def set_timeout(self, timeout: int):
        self.timeout = timeout

    def set_llm_model(self, model_name: str):
        self.llm_model = model_name
        self.llm_interface = LLMInterface(self.sts, model_name=self.llm_model, bit_width=self.bit_width)

    def reset(self):
        self.solve_time = 0.0
        self.result = None
        self.tried_candidates.clear()

    def __str__(self) -> str:
        return f"LLM4InvProver(model={self.llm_model}, timeout={self.timeout})"

    def __repr__(self) -> str:
        return self.__str__()