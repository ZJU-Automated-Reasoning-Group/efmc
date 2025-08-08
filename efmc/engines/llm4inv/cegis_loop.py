"""
Simplified CEGIS Loop for LLM4Inv

1. Uses LLM to propose concrete invariant candidates
2. Checks each candidate for validity using SMT solver
3. If candidate fails, extracts counterexamples and refines approach
4. Iterates until a valid invariant is found or budget exhausted
"""

import logging
import time
from typing import List, Optional, Tuple, Dict, Any
import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult, check_invariant
from .llm_interface import LLMInterface

logger = logging.getLogger(__name__)


class CEGISLoop:
    """
    Simplified CEGIS loop for LLM-guided invariant synthesis.
    
    This class coordinates the iterative process of concrete invariant generation
    and verification using counterexample-guided inductive synthesis.
    """
    
    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        self.max_iterations = kwargs.get('max_iterations', 10)
        self.max_candidates_per_iteration = kwargs.get('max_candidates_per_iteration', 5)
        self.timeout = kwargs.get('timeout', 600)
        self.bit_width = kwargs.get('bit_width', 32)
        
        # Initialize components
        self.llm_interface = LLMInterface(sts, **kwargs)
        
        # State tracking
        self.failed_candidates = []
        self.counterexamples = []
        
        # Statistics
        self.stats = {
            'total_iterations': 0,
            'successful_iterations': 0,
            'total_candidates_generated': 0,
            'successful_candidates': 0,
            'total_time': 0,
            'llm_time': 0,
            'smt_time': 0,
            'counterexample_count': 0
        }
        
        # Timing
        self.start_time = None
    
    def synthesize_invariant(self, program_code: str = "") -> Optional[z3.ExprRef]:
        """
        Main CEGIS loop for invariant synthesis.
        
        Args:
            program_code: Optional program description for LLM
            
        Returns:
            Synthesized invariant or None if synthesis fails
        """
        self.start_time = time.time()
        
        try:
            for iteration in range(self.max_iterations):
                self.stats['total_iterations'] += 1
                
                logger.info(f"CEGIS iteration {iteration + 1}/{self.max_iterations}")
                
                # Check timeout
                if time.time() - self.start_time > self.timeout:
                    logger.warning("CEGIS timeout reached")
                    break
                
                # Attempt synthesis for this iteration
                result = self._cegis_iteration(program_code, iteration)
                
                if result is not None:
                    self.stats['successful_iterations'] += 1
                    logger.info(f"CEGIS synthesis successful after {iteration + 1} iterations")
                    return result
                
                # If we have counterexamples, update the approach
                if self.counterexamples:
                    self._update_approach()
            
            logger.info("CEGIS synthesis failed after maximum iterations")
            return None
            
        finally:
            self.stats['total_time'] = time.time() - self.start_time
    
    def _cegis_iteration(self, program_code: str, iteration: int) -> Optional[z3.ExprRef]:
        """Single iteration of the CEGIS loop"""
        
        # Generate concrete candidates using LLM
        llm_start = time.time()
        
        counterexample_str = self._format_counterexamples() if self.counterexamples else ""
        
        candidates = self.llm_interface.generate_concrete_invariants(
            program_code=program_code,
            failed_candidates=self.failed_candidates[-5:] if self.failed_candidates else [],  # Last 5 failures
            max_candidates=self.max_candidates_per_iteration,
        )
        
        self.stats['llm_time'] += time.time() - llm_start
        self.stats['total_candidates_generated'] += len(candidates)
        
        if not candidates:
            logger.warning(f"No candidates generated in iteration {iteration + 1}")
            return None
        
        logger.info(f"Generated {len(candidates)} candidates in iteration {iteration + 1}")
        
        # Try to verify each candidate
        for i, (cand_str, cand_expr) in enumerate(candidates):
            logger.info(f"Checking candidate {i + 1}/{len(candidates)}: {cand_str}")
            
            smt_start = time.time()
            
            # Check if candidate is a valid invariant
            if check_invariant(self.sts, cand_expr, cand_expr):
                self.stats['smt_time'] += time.time() - smt_start
                self.stats['successful_candidates'] += 1
                logger.info(f"Candidate verification successful: {cand_str}")
                return cand_expr
            else:
                self.stats['smt_time'] += time.time() - smt_start
                # Candidate failed, record failure
                self.failed_candidates.append(cand_str)
                
                # Extract counterexamples from failed candidate
                counterexamples = self._extract_counterexamples(cand_expr)
                self.counterexamples.extend(counterexamples)
                self.stats['counterexample_count'] += len(counterexamples)
        
        return None
    
    def _extract_counterexamples(self, failed_candidate: z3.ExprRef) -> List[Tuple[z3.ModelRef, z3.ModelRef]]:
        """Extract counterexamples from failed candidate"""
        # This is a simplified version - in practice, we'd need to run
        # bounded model checking or similar to find concrete counterexamples
        
        # For now, return empty list as counterexample extraction
        # would require integration with BMC or similar tools
        return []
    
    def _format_counterexamples(self) -> str:
        """Format counterexamples for LLM consumption"""
        if not self.counterexamples:
            return ""
        
        formatted = []
        for i, (pre_state, post_state) in enumerate(self.counterexamples[-5:]):  # Last 5 counterexamples
            pre_vals = {str(var): pre_state[var] for var in self.sts.variables if var in pre_state}
            post_vals = {str(var): post_state[var] for var in self.sts.variables if var in post_state}
            
            formatted.append(f"Counterexample {i + 1}:")
            formatted.append(f"  Pre-state: {pre_vals}")
            formatted.append(f"  Post-state: {post_vals}")
        
        return "\n".join(formatted)
    
    def _update_approach(self):
        """Update synthesis approach based on counterexamples"""
        # Simple approach: limit the number of stored counterexamples
        if len(self.counterexamples) > 10:
            self.counterexamples = self.counterexamples[-10:]  # Keep last 10
        
        # Limit failed candidates
        if len(self.failed_candidates) > 10:
            self.failed_candidates = self.failed_candidates[-10:]  # Keep last 10
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get CEGIS loop statistics"""
        stats = self.stats.copy()
        
        # Add computed statistics
        if self.stats['total_iterations'] > 0:
            stats['success_rate'] = self.stats['successful_iterations'] / self.stats['total_iterations']
        else:
            stats['success_rate'] = 0.0
        
        if self.stats['total_candidates_generated'] > 0:
            stats['candidate_success_rate'] = self.stats['successful_candidates'] / self.stats['total_candidates_generated']
        else:
            stats['candidate_success_rate'] = 0.0
        
        return stats
    
    def reset(self):
        """Reset the CEGIS loop state"""
        self.failed_candidates.clear()
        self.counterexamples.clear()
        
        # Reset statistics
        for key in self.stats:
            self.stats[key] = 0
        
        self.start_time = None 