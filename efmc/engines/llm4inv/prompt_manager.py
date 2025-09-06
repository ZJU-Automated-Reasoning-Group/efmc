"""
Prompt Manager for LLM4Inv

This module contains all invariant-specific prompts and parsing logic,
keeping them separate from the generic LLM interface.
"""

import json
import re
import logging
from typing import List, Optional, Tuple, Dict, Any
import z3

from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


def extract_bit_width_from_sts(sts: TransitionSystem) -> int:
    """Extract bit width from TransitionSystem variables."""
    if not sts.variables:
        return 32  # Default fallback
    
    # Find the first bit-vector variable and extract its width
    for var in sts.variables:
        if z3.is_bv_sort(var.sort()):
            return var.sort().size()
    
    # If no bit-vector variables found, return default
    return 32


class InvariantPromptManager:
    """
    Manages invariant-specific prompts and response parsing for LLM4Inv.
    
    This class handles all the domain-specific logic for generating
    invariant synthesis prompts and parsing LLM responses.
    """
    
    def __init__(self, sts: TransitionSystem, bit_width: Optional[int] = None):
        self.sts = sts
        self.bit_width = bit_width or extract_bit_width_from_sts(sts)
        self.variables = [str(var) for var in self.sts.variables]
    
    def generate_invariant_prompt(
        self,
        program_code: str = "",
        failed_candidates: Optional[List[str]] = None,
        max_candidates: int = 5
    ) -> str:
        """
        Generate a prompt for invariant synthesis.
        
        Args:
            program_code: The program code to analyze
            failed_candidates: Previously failed candidates to avoid
            max_candidates: Maximum number of candidates to generate
            
        Returns:
            The formatted prompt string
        """
        failed_candidates = failed_candidates or []
        
        failed_candidates_section = (
            'The following candidates failed previously and should be avoided or strengthened:\n' + 
            '\n'.join('- ' + c for c in failed_candidates)
            if failed_candidates else ''
        )
        
        prompt = f"""You are an expert in program verification. Propose up to {max_candidates} concrete inductive invariant candidates for the following program. Do NOT use holes or placeholders. Use only variables: {', '.join(self.variables)}.

Program:
```
{program_code}
```

{failed_candidates_section}

Return candidates in Z3 Python API format. Use the following format for each candidate:
- For equality: var1 == var2 or var1 == z3.BitVecVal(value, bitwidth)
- For inequalities: z3.ULE(var1, var2) or z3.ULT(var1, var2) for unsigned, z3.LE(var1, var2) for signed
- For bitwise operations: var1 & z3.BitVecVal(mask, bitwidth) or var1 | z3.BitVecVal(mask, bitwidth)
- For logical operations: z3.And(expr1, expr2) or z3.Or(expr1, expr2)

Return a JSON object with an array field named "candidates" that contains Z3 Python expressions as strings. Example:
```json
{{"candidates": ["x == z3.BitVecVal(0, 32)", "z3.ULE(x, z3.BitVecVal(100, 32))", "z3.And(z3.UGE(x, z3.BitVecVal(0, 32)), z3.ULE(x, z3.BitVecVal(255, 32)))"]}}
```

Alternative: You can also return S-expressions in SMT-LIB format if Z3 Python format is too complex:
```json
{{"candidates": ["(= x #x00000000)", "(bvule x #x00000064)", "(and (bvuge x #x00000000) (bvule x #x000000ff))"]}}
```
"""
        return prompt
    
    def parse_invariant_response(self, response: str) -> List[Tuple[str, z3.ExprRef]]:
        """
        Parse LLM response to extract invariant candidates.
        
        Args:
            response: The raw response from the LLM
            
        Returns:
            List of (original_string, z3_expr) pairs
        """
        try:
            # Extract JSON from response
            json_match = re.search(r'```json\s*(\{.*?\})\s*```', response, re.DOTALL)
            if not json_match:
                json_match = re.search(r'\{.*\}', response, re.DOTALL)
            if not json_match:
                logger.warning(f"No JSON found in response: {response[:100]}...")
                return []
            
            json_str = json_match.group(1) if json_match.group(1) else json_match.group(0)
            logger.info(f"Extracted JSON: {json_str}")
            
            parsed = json.loads(json_str)
            candidate_strs = parsed.get("candidates", [])
            logger.info(f"Parsed candidates: {candidate_strs}")
        except Exception as e:
            logger.error(f"Failed to parse invariant candidates: {e}")
            logger.error(f"Response was: {response}")
            return []

        pairs = []
        for s in candidate_strs:
            expr = self._parse_candidate_to_z3(s)
            if expr is not None:
                pairs.append((s, expr))
        
        return pairs
    
    def _parse_candidate_to_z3(self, s: str) -> Optional[z3.ExprRef]:
        """Parse candidate expressions to Z3 expressions."""
        try:
            s = s.strip()
            var_map = {str(var): var for var in self.sts.variables}
            
            # Try Z3 Python API evaluation
            try:
                safe_globals = {'z3': z3, '__builtins__': {}, **var_map}
                expr = eval(s, safe_globals)
                if isinstance(expr, z3.ExprRef):
                    return expr
            except:
                pass
            
            # Try SMT-LIB parsing
            try:
                if s.startswith('(') or s.startswith('=') or s.startswith('#x') or s.isdigit() or '#' in s:
                    decls = [f"(declare-fun {str(var)} () (_ BitVec {var.sort().size()}))" 
                            if z3.is_bv_sort(var.sort()) else f"(declare-fun {str(var)} () Int)"
                            for var in self.sts.variables]
                    smt = "\n".join(decls) + f"\n(assert {s})\n"
                    expr = z3.parse_smt2_string(smt)
                    if hasattr(expr, '__len__') and len(expr) > 0:
                        return expr[0]
            except:
                pass
            
            return None
        except:
            return None
    
    def create_prompt_generator(
        self,
        program_code: str = "",
        failed_candidates: Optional[List[str]] = None,
        max_candidates: int = 5
    ):
        """
        Create a prompt generator function for use with the generic LLM interface.
        
        Args:
            program_code: The program code to analyze
            failed_candidates: Previously failed candidates to avoid
            max_candidates: Maximum number of candidates to generate
            
        Returns:
            A function that generates the prompt when called
        """
        def prompt_generator():
            return self.generate_invariant_prompt(program_code, failed_candidates, max_candidates)
        
        return prompt_generator
    
    def create_response_parser(self):
        """
        Create a response parser function for use with the generic LLM interface.
        
        Returns:
            A function that parses LLM responses into candidate pairs
        """
        def response_parser(response: str):
            return self.parse_invariant_response(response)
        
        return response_parser
