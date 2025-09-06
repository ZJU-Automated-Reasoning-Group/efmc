"""
Generic LLM Interface for CEGIS Loop Communication

This interface handles communication between the CEGIS loop and LLM providers
without containing domain-specific prompts or parsing logic.
"""

import logging
from typing import List, Dict, Any, Optional, Tuple, Callable
import z3

from efmc.llmtools.llm_utils import LLM
from efmc.llmtools.llm_local import LLMLocal
from efmc.llmtools.logger import Logger
from efmc.sts import TransitionSystem
from efmc.engines.llm4inv.prompt_manager import extract_bit_width_from_sts

logger = logging.getLogger(__name__)


class LLMInterface:
    """
    Generic LLM interface for CEGIS loop communication.
    
    This interface provides a clean abstraction for LLM communication
    without containing domain-specific prompts or parsing logic.
    The actual prompt generation and response parsing are delegated
    to external functions provided by the caller.
    """
    
    def __init__(self, sts: TransitionSystem, model_name: str = "deepseek-v3", **kwargs):
        self.sts = sts
        self.model_name = model_name
        self.temperature = kwargs.get('temperature', 0.1)
        self.llm_provider = kwargs.get('llm_provider', 'local')
        self.llm_model = kwargs.get('llm_model', 'qwen/qwen3-coder-30b')
        self.bit_width = kwargs.get('bit_width') or extract_bit_width_from_sts(sts)
        
        # Initialize LLM
        self.logger = Logger("llm4inv.log")
        
        # Choose between local and online LLM based on provider
        if self.llm_provider == 'local':
            self.llm = LLMLocal(
                offline_model_name=self.llm_model,
                logger=self.logger,
                temperature=self.temperature,
                max_output_length=kwargs.get('max_output_length', 4096),
                measure_cost=kwargs.get('measure_cost', False),
                provider=kwargs.get('local_provider', 'lm-studio')
            )
        else:
            self.llm = LLM(model_name, self.logger, temperature=self.temperature)
        
        # Statistics
        self.stats = {
            'total_llm_calls': 0,
            'successful_generations': 0,
            'total_candidates_generated': 0,
            'refinement_calls': 0
        }
    
    def generate_candidates(
        self,
        prompt_generator: Callable[[], str],
        response_parser: Callable[[str], List[Tuple[str, z3.ExprRef]]],
        context: Optional[Dict[str, Any]] = None
    ) -> List[Tuple[str, z3.ExprRef]]:
        """
        Generic method to generate candidates using LLM.
        
        Args:
            prompt_generator: Function that generates the prompt for the LLM
            response_parser: Function that parses the LLM response into candidate pairs
            context: Optional context data for the generation
            
        Returns:
            List of (original_string, z3_expr) pairs
        """
        context = context or {}
        
        # Generate prompt using the provided function
        prompt = prompt_generator()
        
        # Call LLM
        self.stats['total_llm_calls'] += 1
        resp, _, _ = self.llm.infer(prompt, is_measure_cost=False)
        
        # Debug logging
        logger.info(f"LLM Response: {resp[:200]}...")
        
        # Parse response using the provided function
        try:
            pairs = response_parser(resp)
            if pairs:
                self.stats['successful_generations'] += 1
                self.stats['total_candidates_generated'] += len(pairs)
            return pairs
        except Exception as e:
            logger.error(f"Failed to parse LLM response: {e}")
            logger.error(f"Response was: {resp}")
            return []

    def call_llm(self, prompt: str, **kwargs) -> str:
        self.stats['total_llm_calls'] += 1
        resp, _, _ = self.llm.infer(prompt, is_measure_cost=kwargs.get('measure_cost', False))
        return resp
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get interface statistics"""
        return self.stats.copy() 