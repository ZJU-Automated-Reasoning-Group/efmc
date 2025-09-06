"""
CEGIS Loop for LLM4Inv - Uses LLM to propose invariant candidates and verifies them iteratively.
"""

import logging
import time
from typing import List, Optional, Tuple, Dict, Any
import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import verify_invariant_with_counterexamples
from efmc.engines.llm4inv.llm_interface import LLMInterface
from efmc.engines.llm4inv.prompt_manager import InvariantPromptManager

logger = logging.getLogger(__name__)


class LLMInvariantCEGIS:
    """CEGIS loop for LLM-guided invariant synthesis."""
    
    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        self.max_iterations = kwargs.get('max_iterations', 10)
        self.max_candidates_per_iteration = kwargs.get('max_candidates_per_iteration', 5)
        self.timeout = kwargs.get('timeout', 600)
        
        # Initialize generic LLM interface
        self.llm_interface = LLMInterface(sts, **kwargs)
        
        # Initialize invariant-specific prompt manager
        self.prompt_manager = InvariantPromptManager(sts, kwargs.get('bit_width'))
        
        self.failed_candidates = []
        self.counterexamples = []
        self.stats = {'iterations': 0, 'candidates': 0, 'successful': 0, 'time': 0}
        self.start_time = None
    
    def synthesize_invariant(self, program_code: str = "") -> Optional[z3.ExprRef]:
        """Main CEGIS loop for invariant synthesis."""
        self.start_time = time.time()
        
        try:
            for iteration in range(self.max_iterations):
                self.stats['iterations'] += 1
                
                if time.time() - self.start_time > self.timeout:
                    break
                
                result = self._cegis_iteration(program_code)
                if result is not None:
                    self.stats['successful'] += 1
                    return result
                
                if self.counterexamples:
                    self._update_approach()
            
            return None
            
        finally:
            self.stats['time'] = time.time() - self.start_time
    
    def _cegis_iteration(self, program_code: str) -> Optional[z3.ExprRef]:
        """Single iteration of the CEGIS loop"""
        # Create prompt generator and response parser for this iteration
        prompt_generator = self.prompt_manager.create_prompt_generator(
            program_code=program_code,
            failed_candidates=self.failed_candidates[-5:],
            max_candidates=self.max_candidates_per_iteration
        )
        response_parser = self.prompt_manager.create_response_parser()
        
        # Generate candidates using the generic interface
        candidates = self.llm_interface.generate_candidates(
            prompt_generator=prompt_generator,
            response_parser=response_parser
        )
        
        self.stats['candidates'] += len(candidates)
        
        for cand_str, cand_expr in candidates:
            is_correct, counterexamples = verify_invariant_with_counterexamples(self.sts, cand_expr)
            if is_correct:
                return cand_expr
            
            self.failed_candidates.append(cand_str)
            self.counterexamples.extend(counterexamples)
        
        return None
    
    def _update_approach(self):
        """Update synthesis approach based on counterexamples"""
        if len(self.counterexamples) > 10:
            self.counterexamples = self.counterexamples[-10:]
        if len(self.failed_candidates) > 10:
            self.failed_candidates = self.failed_candidates[-10:]
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get CEGIS loop statistics"""
        stats = self.stats.copy()
        if self.stats['iterations'] > 0:
            stats['success_rate'] = self.stats['successful'] / self.stats['iterations']
        if self.stats['candidates'] > 0:
            stats['candidate_success_rate'] = self.stats['successful'] / self.stats['candidates']
        return stats
    
    def reset(self):
        """Reset the CEGIS loop state"""
        self.failed_candidates.clear()
        self.counterexamples.clear()
        for key in self.stats:
            self.stats[key] = 0
        self.start_time = None
        