"""
CEGIS Loop for LLM4Inv - Uses LLM to propose invariant candidates and verifies them iteratively.
"""

import logging
import time
from typing import List, Optional, Tuple, Dict, Any
import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import check_invariant
from efmc.engines.llm4inv.llm_interface import LLMInterface

logger = logging.getLogger(__name__)


class LLMInvariantCEGIS:
    """CEGIS loop for LLM-guided invariant synthesis."""
    
    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        self.max_iterations = kwargs.get('max_iterations', 10)
        self.max_candidates_per_iteration = kwargs.get('max_candidates_per_iteration', 5)
        self.timeout = kwargs.get('timeout', 600)
        
        self.llm_interface = LLMInterface(sts, **kwargs)
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
        candidates = self.llm_interface.generate_concrete_invariants(
            program_code=program_code,
            failed_candidates=self.failed_candidates[-5:],
            max_candidates=self.max_candidates_per_iteration,
        )
        
        self.stats['candidates'] += len(candidates)
        
        for cand_str, cand_expr in candidates:
            if check_invariant(self.sts, cand_expr, cand_expr):
                return cand_expr
            
            self.failed_candidates.append(cand_str)
            counterexamples = self._extract_counterexamples(cand_expr)
            self.counterexamples.extend(counterexamples)
        
        return None
    
    def _extract_counterexamples(self, failed_candidate: z3.ExprRef) -> List[Tuple[z3.ModelRef, z3.ModelRef]]:
        """Extract counterexamples from failed candidate"""
        counterexamples = []
        solver = z3.Solver()
        
        # Check initial states
        if self.sts.init is not None:
            solver.push()
            solver.add(z3.Not(failed_candidate), self.sts.init)
            if solver.check() == z3.sat:
                counterexamples.append((solver.model(), None))
            solver.pop()
        
        # Check inductive step
        if self.sts.trans is not None:
            solver.push()
            primed_invariant = z3.substitute(failed_candidate, 
                [(var, var.prime()) for var in self.sts.variables])
            solver.add(failed_candidate, self.sts.trans, z3.Not(primed_invariant))
            
            if solver.check() == z3.sat:
                model = solver.model()
                pre_state = {var: model[var] for var in self.sts.variables if var in model}
                post_state = {var: model[var.prime()] for var in self.sts.variables if var.prime() in model}
                if pre_state and post_state:
                    counterexamples.append((pre_state, post_state))
            solver.pop()
        
        return counterexamples
    
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
        