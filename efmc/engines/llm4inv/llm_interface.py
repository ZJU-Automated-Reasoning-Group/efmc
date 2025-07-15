"""
LLM Interface for Template Generation and Invariant Synthesis
"""

import logging
import json
import re
from typing import List, Dict, Any, Optional, Tuple
import z3

from efmc.llm.llm_tool import LLMTool, LLMToolInput, LLMToolOutput
from efmc.llm.llm_utils import LLM
from efmc.sts import TransitionSystem
from .template_dsl import TemplateInvariant, TemplateParser

logger = logging.getLogger(__name__)


class LLMInterface:
    """
    Unified LLM interface for template generation and invariant synthesis.
    Combines template generation and refinement in a single class.
    """
    
    def __init__(self, sts: TransitionSystem, model_name: str = "deepseek-v3", **kwargs):
        self.sts = sts
        self.model_name = model_name
        self.temperature = kwargs.get('temperature', 0.1)
        self.max_templates = kwargs.get('max_templates', 3)
        self.bit_width = kwargs.get('bit_width', 32)
        
        # Initialize LLM and parser
        self.llm = LLM(model_name, temperature=self.temperature)
        self.parser = TemplateParser(self.bit_width)
        
        # Set up variables from STS
        self._setup_variables()
        
        # Statistics
        self.stats = {
            'total_llm_calls': 0,
            'successful_generations': 0,
            'total_templates_generated': 0,
            'refinement_calls': 0
        }
    
    def _setup_variables(self):
        """Extract variables from transition system"""
        variables = {}
        for var_name, var_expr in self.sts.variables.items():
            variables[var_name] = var_expr
        self.parser.set_variables(variables)
    
    def generate_templates(self, program_code: str = "", counterexamples: str = "") -> List[TemplateInvariant]:
        """
        Generate invariant templates using LLM.
        
        Args:
            program_code: Program source code or description
            counterexamples: String describing failed attempts
            
        Returns:
            List of parsed template invariants
        """
        self.stats['total_llm_calls'] += 1
        
        # Create prompt
        prompt = self._create_prompt(program_code, counterexamples)
        
        # Get LLM response
        response = self.llm.generate(prompt)
        
        # Parse templates
        templates = self._parse_templates(response)
        
        self.stats['total_templates_generated'] += len(templates)
        if templates:
            self.stats['successful_generations'] += 1
            
        return templates
    
    def refine_templates(self, failed_templates: List[str], counterexamples: str) -> List[TemplateInvariant]:
        """
        Refine templates based on counterexamples.
        
        Args:
            failed_templates: Previously failed template strings
            counterexamples: Counterexample information
            
        Returns:
            List of refined template invariants
        """
        self.stats['refinement_calls'] += 1
        
        # Create refinement prompt
        prompt = self._create_refinement_prompt(failed_templates, counterexamples)
        
        # Get LLM response
        response = self.llm.generate(prompt)
        
        # Parse refined templates
        templates = self._parse_templates(response)
        
        self.stats['total_templates_generated'] += len(templates)
        return templates
    
    def _create_prompt(self, program_code: str, counterexamples: str = "") -> str:
        """Create prompt for template generation"""
        variables = list(self.sts.variables.keys())
        
        prompt = f"""You are an expert in program verification. Generate {self.max_templates} invariant templates for this {self.bit_width}-bit program.

## DSL Grammar
- Conjunction: expr1 && expr2
- Equality: expr == expr  
- Unsigned comparison: expr <u expr, expr <=u expr
- Bitmask: (expr & C?) == C?
- Population count: popcnt(expr) OP K?
- Rotation: (expr <<< K?) OP expr
- Holes: C? (constants), K? (shift amounts)

## Program
Variables: {', '.join(variables)}
```
{program_code}
```

{f"## Failed Attempts\\n{counterexamples}\\n" if counterexamples else ""}

Generate templates as JSON:
```json
{{"templates": ["template1", "template2", "template3"]}}
```

Focus on bit-level patterns, variable relationships, and structural invariants."""
        
        return prompt
    
    def _create_refinement_prompt(self, failed_templates: List[str], counterexamples: str) -> str:
        """Create prompt for template refinement"""
        return f"""The following templates failed:
{chr(10).join(f"- {t}" for t in failed_templates)}

Counterexamples:
{counterexamples}

Generate {self.max_templates} refined templates that avoid these failures:
```json
{{"templates": ["refined1", "refined2", "refined3"]}}
```"""
    
    def _parse_templates(self, response: str) -> List[TemplateInvariant]:
        """Parse LLM response into template invariants"""
        try:
            # Extract JSON
            json_match = re.search(r'```json\s*(\{.*?\})\s*```', response, re.DOTALL)
            if not json_match:
                json_match = re.search(r'\{.*\}', response, re.DOTALL)
            
            if not json_match:
                return []
            
            parsed = json.loads(json_match.group(1) if json_match.group(1) else json_match.group(0))
            template_strings = parsed.get("templates", [])
            
            # Parse each template
            templates = []
            for template_str in template_strings:
                template = self.parser.parse_template(template_str)
                if template:
                    templates.append(template)
                    
            return templates
            
        except Exception as e:
            logger.error(f"Failed to parse templates: {e}")
            return []
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get interface statistics"""
        return self.stats.copy() 