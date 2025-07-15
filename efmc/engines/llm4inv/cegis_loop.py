"""
Simplified CEGIS Loop for LLM4Inv

1. Uses LLM to propose template structures
2. Uses SMT solver to complete templates (fill holes)
3. If completion fails, extracts counterexamples and refines templates
4. Iterates until a valid invariant is found or budget exhausted
"""

import logging
import time
from typing import List, Optional, Tuple, Dict, Any
import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult
from .template_dsl import TemplateInvariant
from .template_completion import TemplateCompletion
from .llm_interface import LLMInterface

logger = logging.getLogger(__name__)


class CEGISLoop:
    """
    Simplified CEGIS loop for LLM-guided invariant synthesis.
    
    This class coordinates the iterative process of template generation,
    completion, and refinement using counterexample-guided inductive synthesis.
    """
    
    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        self.max_iterations = kwargs.get('max_iterations', 10)
        self.max_templates_per_iteration = kwargs.get('max_templates_per_iteration', 3)
        self.timeout = kwargs.get('timeout', 600)
        self.bit_width = kwargs.get('bit_width', 32)
        
        # Initialize components
        self.llm_interface = LLMInterface(sts, **kwargs)
        self.template_completion = TemplateCompletion(sts, **kwargs)
        
        # State tracking
        self.failed_templates = []
        self.counterexamples = []
        
        # Statistics
        self.stats = {
            'total_iterations': 0,
            'successful_iterations': 0,
            'total_templates_generated': 0,
            'successful_completions': 0,
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
        
        # Generate templates using LLM
        llm_start = time.time()
        
        counterexample_str = self._format_counterexamples() if self.counterexamples else ""
        
        if iteration == 0:
            # First iteration: generate fresh templates
            templates = self.llm_interface.generate_templates(program_code, counterexample_str)
        else:
            # Subsequent iterations: refine based on failures
            failed_template_strs = [self._template_to_string(t) for t in self.failed_templates[-3:]]  # Last 3 failures
            templates = self.llm_interface.refine_templates(failed_template_strs, counterexample_str)
        
        self.stats['llm_time'] += time.time() - llm_start
        self.stats['total_templates_generated'] += len(templates)
        
        if not templates:
            logger.warning(f"No templates generated in iteration {iteration + 1}")
            return None
        
        logger.info(f"Generated {len(templates)} templates in iteration {iteration + 1}")
        
        # Try to complete each template
        for i, template in enumerate(templates):
            logger.info(f"Attempting completion of template {i + 1}/{len(templates)}")
            
            smt_start = time.time()
            
            # Use traces from counterexamples if available
            traces = self._extract_traces_from_counterexamples()
            invariant = self.template_completion.complete_template(template, traces)
            
            self.stats['smt_time'] += time.time() - smt_start
            
            if invariant is not None:
                self.stats['successful_completions'] += 1
                logger.info(f"Template completion successful: {invariant}")
                return invariant
            else:
                # Template completion failed, record failure
                self.failed_templates.append(template)
                
                # Extract counterexamples from failed completion
                counterexamples = self._extract_counterexamples(template)
                self.counterexamples.extend(counterexamples)
                self.stats['counterexample_count'] += len(counterexamples)
        
        return None
    
    def _extract_counterexamples(self, failed_template: TemplateInvariant) -> List[Tuple[z3.ModelRef, z3.ModelRef]]:
        """Extract counterexamples from failed template completion"""
        # This is a simplified version - in practice, we'd need to run
        # bounded model checking or similar to find concrete counterexamples
        
        # For now, return empty list as counterexample extraction
        # would require integration with BMC or similar tools
        return []
    
    def _extract_traces_from_counterexamples(self) -> List[Tuple[z3.ModelRef, z3.ModelRef]]:
        """Convert counterexamples to execution traces"""
        # Convert stored counterexamples to trace format
        return self.counterexamples
    
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
    
    def _template_to_string(self, template: TemplateInvariant) -> str:
        """Convert template back to string representation"""
        atom_strs = []
        for atom in template.atoms:
            # Simplified string conversion
            atom_strs.append(f"{atom.atom_type.name}_atom")
        
        connector = " && " if template.conjunction else " || "
        return connector.join(atom_strs)
    
    def _update_approach(self):
        """Update synthesis approach based on counterexamples"""
        # Simple approach: limit the number of stored counterexamples
        if len(self.counterexamples) > 10:
            self.counterexamples = self.counterexamples[-10:]  # Keep last 10
        
        # Limit failed templates
        if len(self.failed_templates) > 5:
            self.failed_templates = self.failed_templates[-5:]  # Keep last 5
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get CEGIS loop statistics"""
        stats = self.stats.copy()
        
        # Add computed statistics
        if self.stats['total_iterations'] > 0:
            stats['success_rate'] = self.stats['successful_iterations'] / self.stats['total_iterations']
        else:
            stats['success_rate'] = 0.0
        
        if self.stats['total_templates_generated'] > 0:
            stats['template_success_rate'] = self.stats['successful_completions'] / self.stats['total_templates_generated']
        else:
            stats['template_success_rate'] = 0.0
        
        return stats
    
    def reset(self):
        """Reset the CEGIS loop state"""
        self.failed_templates.clear()
        self.counterexamples.clear()
        
        # Reset statistics
        for key in self.stats:
            self.stats[key] = 0
        
        self.start_time = None 