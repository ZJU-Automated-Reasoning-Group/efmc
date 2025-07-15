"""
LLM4Inv: LLM-guided Invariant Synthesis Engine

This module implements a simplified "LLM proposes structure, SMT fills holes" approach:
- LLM provides structural patterns and qualitative insights
- SMT solver handles quantitative bit-precise arithmetic
- CEGIS loop iteratively refines templates based on counterexamples

The module has been streamlined to focus on core functionality while maintaining
the essential hybrid LLM-SMT approach for invariant generation.
"""

from .llm4inv_prover import LLM4InvProver
from .template_dsl import TemplateGrammar, TemplateParser
from .template_completion import TemplateCompletion
from .cegis_loop import CEGISLoop
from .llm_interface import LLMInterface

__all__ = [
    'LLM4InvProver',
    'TemplateGrammar', 
    'TemplateParser',
    'TemplateCompletion',
    'CEGISLoop',
    'LLMInterface'
] 