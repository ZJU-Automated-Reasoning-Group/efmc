"""
LLM4Inv Prover - Lightweight Interface

This is a simplified interface that wraps the CEGIS loop for easy usage.
It provides a clean API while delegating the actual synthesis work to LLMInvariantCEGIS.
"""

import logging
from typing import Optional, Dict, Any

import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult
from .cegis_loop import LLMInvariantCEGIS
from .prompt_manager import extract_bit_width_from_sts

logger = logging.getLogger(__name__)


class LLM4InvProver:
    """
    LLM-based invariant synthesis.
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        
        # Store configuration
        self.timeout = kwargs.get('timeout', 600)
        self.max_iterations = kwargs.get('max_iterations', 10)
        self.bit_width = kwargs.get('bit_width') or extract_bit_width_from_sts(sts)
        self.llm_model = kwargs.get('llm_model', 'deepseek-v3')
        
        # Initialize the CEGIS loop with the same configuration
        self.cegis = LLMInvariantCEGIS(sts, **kwargs)
        
        # Results
        self.result: Optional[VerificationResult] = None
        self.solve_time = 0.0
    
    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        if timeout is not None:
            self.timeout = timeout
            self.cegis.timeout = timeout

        logger.info("Starting LLM4Inv synthesis via CEGIS loop")
        
        # Generate program description for the LLM
        program_description = self._generate_program_description()
        
        # Use CEGIS loop for synthesis
        invariant = self.cegis.synthesize_invariant(program_description)
        
        # Convert result to VerificationResult format
        if invariant is not None:
            self.result = VerificationResult(True, invariant)
            logger.info(f"LLM4Inv synthesis successful: {invariant}")
        else:
            self.result = VerificationResult(False, None)
            logger.warning("LLM4Inv synthesis failed")
        
        # Get timing from CEGIS loop
        self.solve_time = self.cegis.stats.get('total_time', 0.0)
        
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
        # Get base statistics
        stats = {
            'solve_time': self.solve_time,
            'timeout': self.timeout,
            'max_iterations': self.max_iterations,
            'bit_width': self.bit_width,
            'llm_model': self.llm_model,
            'success': self.result.is_safe if self.result else False,
        }
        
        # Add CEGIS loop statistics
        cegis_stats = self.cegis.get_statistics()
        stats.update(cegis_stats)
        
        return stats

    def set_timeout(self, timeout: int):
        """Set timeout for synthesis"""
        self.timeout = timeout
        self.cegis.timeout = timeout

    def set_llm_model(self, model_name: str):
        """Set LLM model for synthesis"""
        self.llm_model = model_name
        # Recreate CEGIS loop with new model
        kwargs = {
            'timeout': self.timeout,
            'max_iterations': self.max_iterations,
            'bit_width': self.bit_width,
            'llm_model': model_name
        }
        self.cegis = LLMInvariantCEGIS(self.sts, **kwargs)

    def reset(self):
        """Reset the prover state"""
        self.result = None
        self.solve_time = 0.0
        self.cegis.reset()

    def __str__(self) -> str:
        return f"LLM4InvProver(model={self.llm_model}, timeout={self.timeout})"

    def __repr__(self) -> str:
        return self.__str__()