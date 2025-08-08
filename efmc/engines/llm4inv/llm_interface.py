"""
LLM Interface for Concrete Invariant Synthesis
"""

import logging
import json
import re
from typing import List, Dict, Any, Optional, Tuple
import z3

from efmc.llmtools.llm_tool import LLMTool, LLMToolInput, LLMToolOutput
from efmc.llmtools.llm_utils import LLM
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


class LLMInterface:
    """
    LLM interface for concrete invariant synthesis.
    Focuses on generating concrete, hole-free invariants for guess-and-check approach.
    """
    
    def __init__(self, sts: TransitionSystem, model_name: str = "deepseek-v3", **kwargs):
        self.sts = sts
        self.model_name = model_name
        self.temperature = kwargs.get('temperature', 0.1)
        self.max_candidates = kwargs.get('max_candidates', 5)
        self.bit_width = kwargs.get('bit_width', 32)
        
        # Initialize LLM
        self.llm = LLM(model_name, temperature=self.temperature)
        
        # Statistics
        self.stats = {
            'total_llm_calls': 0,
            'successful_generations': 0,
            'total_candidates_generated': 0,
            'refinement_calls': 0
        }
    
    def generate_concrete_invariants(
        self,
        program_code: str = "",
        failed_candidates: Optional[List[str]] = None,
        max_candidates: int = 5,
    ) -> List[Tuple[str, z3.ExprRef]]:
        """
        Ask the LLM to propose concrete (hole-free) invariant candidates as plain
        Z3-like expressions over current variables, and parse them to Z3.

        Returns a list of pairs (original_string, z3_expr).
        """
        failed_candidates = failed_candidates or []

        variables = list(self.sts.variables.keys())
        failed_candidates_section = 'The following candidates failed previously and should be avoided or strengthened:\n' + '\n'.join('- ' + c for c in failed_candidates) if failed_candidates else ''
        
        prompt = f"""You are an expert in program verification. Propose up to {max_candidates} concrete inductive invariant candidates for the following program. Do NOT use holes or placeholders. Use only variables: {', '.join(variables)}. Use bit-vector syntax compatible with Z3Py (e.g., bv operations &, |, ^, +, -, ==, ULE, ULT). Use parentheses to clarify precedence.

Program:
```
{program_code}
```

{failed_candidates_section}

Return a JSON object with an array field named "candidates" that contains strings of formulas. Example:
```json
{{"candidates": ["x == y", "(x & 255) == 0", "x <=u y"]}}
```
"""

        self.stats['total_llm_calls'] += 1
        resp = self.llm.generate(prompt)

        try:
            json_match = re.search(r'```json\s*(\{.*?\})\s*```', resp, re.DOTALL)
            if not json_match:
                json_match = re.search(r'\{.*\}', resp, re.DOTALL)
            if not json_match:
                return []
            parsed = json.loads(json_match.group(1) if json_match.group(1) else json_match.group(0))
            candidate_strs = parsed.get("candidates", [])
        except Exception as e:
            logger.error(f"Failed to parse concrete candidates: {e}")
            return []

        pairs: List[Tuple[str, z3.ExprRef]] = []
        for s in candidate_strs:
            expr = self._parse_candidate_to_z3(s)
            if expr is not None:
                pairs.append((s, expr))
                self.stats['total_candidates_generated'] += 1
        
        if pairs:
            self.stats['successful_generations'] += 1
            
        return pairs

    def _parse_candidate_to_z3(self, s: str) -> Optional[z3.ExprRef]:
        """
        Very lightweight parser for a subset of Z3Py-like formulas suitable for BV invariants.
        We map variable names using the STS variable dict, and otherwise fall back to z3.parse_smt2_string when possible.
        """
        try:
            # Try to parse as SMT-LIB by wrapping as an assertion over declared variables
            decls = []
            for vname, vexpr in self.sts.variables.items():
                sort = vexpr.sort()
                if z3.is_bv_sort(sort):
                    decls.append(f"(declare-fun {vname} () (_ BitVec {sort.size()}))")
                else:
                    # Fallback to int for non-BV if any
                    decls.append(f"(declare-fun {vname} () Int)")
            smt = "\n".join(decls) + f"\n(assert {s})\n"
            expr = z3.parse_smt2_string(smt)
            # parse_smt2_string returns a list of assertions
            if isinstance(expr, list) and expr:
                return expr[0]
            return None
        except Exception as e:
            logger.debug(f"Failed to parse candidate '{s}': {e}")
            return None
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get interface statistics"""
        return self.stats.copy() 