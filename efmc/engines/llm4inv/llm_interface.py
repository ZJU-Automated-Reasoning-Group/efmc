"""
LLM Interface for Concrete Invariant Synthesis
"""

import logging
import json
import re
from typing import List, Dict, Any, Optional, Tuple
import z3

from efmc.llmtools.llm_utils import LLM
from efmc.llmtools.llm_local import LLMLocal
from efmc.llmtools.logger import Logger
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
        self.llm_provider = kwargs.get('llm_provider', 'local')
        self.llm_model = kwargs.get('llm_model', 'qwen/qwen3-coder-30b')

        self.bit_width = kwargs.get('bit_width', 32)
        
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

        variables = [str(var) for var in self.sts.variables]
        failed_candidates_section = 'The following candidates failed previously and should be avoided or strengthened:\n' + '\n'.join('- ' + c for c in failed_candidates) if failed_candidates else ''
        
        prompt = f"""You are an expert in program verification. Propose up to {max_candidates} concrete inductive invariant candidates for the following program. Do NOT use holes or placeholders. Use only variables: {', '.join(variables)}.

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

        self.stats['total_llm_calls'] += 1
        resp, _, _ = self.llm.infer(prompt, is_measure_cost=False)
        
        # Debug logging
        logger.info(f"LLM Response: {resp[:200]}...")  # Log first 200 chars

        try:
            json_match = re.search(r'```json\s*(\{.*?\})\s*```', resp, re.DOTALL)
            if not json_match:
                json_match = re.search(r'\{.*\}', resp, re.DOTALL)
            if not json_match:
                logger.warning(f"No JSON found in response: {resp[:100]}...")
                return []
            
            json_str = json_match.group(1) if json_match.group(1) else json_match.group(0)
            logger.info(f"Extracted JSON: {json_str}")
            
            parsed = json.loads(json_str)
            candidate_strs = parsed.get("candidates", [])
            logger.info(f"Parsed candidates: {candidate_strs}")
        except Exception as e:
            logger.error(f"Failed to parse concrete candidates: {e}")
            logger.error(f"Response was: {resp}")
            return []

        pairs = []
        for s in candidate_strs:
            expr = self._parse_candidate_to_z3(s)
            if expr is not None:
                pairs.append((s, expr))
                self.stats['total_candidates_generated'] += 1
        
        if pairs:
            self.stats['successful_generations'] += 1
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
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get interface statistics"""
        return self.stats.copy() 