"""
Danger Invariant Synthesis Engine

Implements danger invariant approach for finding bugs by synthesizing invariants
that over-approximate states leading to errors. If init ⇒ D, proves unsafety.
"""

import logging
import time
from typing import Optional, Dict, Any, List

import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult

logger = logging.getLogger(__name__)


class DangerInvariantProver:
    """Danger invariant synthesis for bug finding and unsafety verification."""
    
    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        self.timeout = kwargs.get('timeout', 300)
        self.max_iterations = kwargs.get('max_iterations', 100)
        self.use_ranking_functions = kwargs.get('use_ranking_functions', True)
        self.template_complexity = kwargs.get('template_complexity', 3)
        
        self.solver = z3.Solver()
        if self.timeout:
            self.solver.set("timeout", self.timeout * 1000)
            
        self.solve_time = 0
        self.iterations = 0
        self.danger_invariant = None
        self.ranking_function = None
        
    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """Main solving interface for danger invariant synthesis."""
        start_time = time.time()
        
        try:
            if timeout:
                self.solver.set("timeout", timeout * 1000)
                
            logger.info("Starting danger invariant synthesis")
            
            # Try multiple synthesis strategies
            strategies = [
                self._try_simple_candidates,
                self._try_template_synthesis,
                self._try_weakened_postcondition
            ]
            
            danger_inv = None
            for strategy in strategies:
                danger_inv = strategy()
                if danger_inv is not None:
                    break
                    
            if danger_inv is None:
                return VerificationResult(False, None, is_unknown=True)
                
            self.danger_invariant = danger_inv
            
            # Synthesize ranking function if enabled
            ranking_fn = None
            if self.use_ranking_functions:
                ranking_fn = self._synthesize_ranking_function(danger_inv)
                self.ranking_function = ranking_fn
            
            # Verify and check for unsafety
            if self._verify_danger_invariant(danger_inv, ranking_fn):
                if self._check_initial_danger(danger_inv):
                    logger.info("UNSAFE: Initial state satisfies danger invariant")
                    return VerificationResult(False, danger_inv, is_unsafe=True)
                else:
                    return VerificationResult(False, None, is_unknown=True)
            else:
                return VerificationResult(False, None, is_unknown=True)
                
        except Exception as e:
            logger.error(f"Error during synthesis: {e}")
            return VerificationResult(False, None, is_unknown=True)
        finally:
            self.solve_time = time.time() - start_time
            
    def _try_simple_candidates(self) -> Optional[z3.ExprRef]:
        """Try simple danger invariant candidates."""
        candidates = [
            z3.Not(self.sts.post),  # Error states
            z3.BoolVal(True),       # Universal danger (fallback)
        ]
        
        # Add variable-specific candidates
        for var in self.sts.variables.values():
            if var.sort() == z3.BoolSort():
                candidates.extend([var, z3.Not(var)])
            elif var.sort().kind() in [z3.Z3_INT_SORT, z3.Z3_REAL_SORT]:
                candidates.extend([var >= 0, var <= 0, var >= 1, var <= -1])
            elif var.sort().kind() == z3.Z3_BV_SORT:
                zero = z3.BitVecVal(0, var.sort().size())
                one = z3.BitVecVal(1, var.sort().size())
                candidates.extend([var == zero, var != zero, z3.UGE(var, one)])
        
        for candidate in candidates:
            if self._check_candidate_danger_invariant(candidate):
                return candidate
        return None
        
    def _try_template_synthesis(self) -> Optional[z3.ExprRef]:
        """Try template-based synthesis with adaptive complexity."""
        # Start with low complexity and increase if needed
        for complexity in range(1, min(self.template_complexity + 1, len(self.sts.variables) + 2)):
            result = self._synthesize_with_complexity(complexity)
            if result is not None:
                return result
        return None
        
    def _try_weakened_postcondition(self) -> Optional[z3.ExprRef]:
        """Try weakened versions of the postcondition."""
        if not self.sts.post:
            return None
            
        # Try different weakenings based on structure
        weakenings = self._generate_weakenings(self.sts.post)
        for weakening in weakenings:
            candidate = z3.Not(weakening)
            if self._check_candidate_danger_invariant(candidate):
                return candidate
        return None
        
    def _generate_weakenings(self, formula: z3.ExprRef) -> List[z3.ExprRef]:
        """Generate weaker versions of a formula."""
        weakenings = []
        
        # If it's a conjunction, try individual conjuncts
        if z3.is_and(formula):
            weakenings.extend(formula.children())
            
        # If it's a disjunction, try the whole formula (already weak)
        elif z3.is_or(formula):
            weakenings.append(formula)
            
        # For other formulas, try structural weakenings
        else:
            weakenings.append(formula)
            
        return weakenings
        
    def _synthesize_with_complexity(self, complexity: int) -> Optional[z3.ExprRef]:
        """Template-based synthesis with specific complexity."""
        solver = z3.Solver()
        if self.timeout:
            solver.set("timeout", self.timeout * 1000)
            
        template_vars = self._create_adaptive_template_variables(complexity)
        danger_template = self._build_adaptive_template(template_vars, complexity)
        danger_template_prime = z3.substitute(
            danger_template, 
            list(zip(list(self.sts.variables.values()), self.sts.prime_variables))
        )
        
        # Add synthesis constraints with relaxed conditions
        constraints = [
            # Inductiveness (must hold)
            z3.ForAll(self.sts.all_variables,
                     z3.Implies(z3.And(danger_template, self.sts.trans), danger_template_prime)),
            # Non-trivial (must be satisfiable)
            z3.Exists(list(self.sts.variables.values()), danger_template)
        ]
        
        # Add error reachability as soft constraint
        if self.sts.post != z3.BoolVal(True):  # Only if postcondition is meaningful
            constraints.append(
                z3.Exists(list(self.sts.variables.values()),
                         z3.And(danger_template, z3.Not(self.sts.post)))
            )
        
        for constraint in constraints:
            solver.add(constraint)
            
        if solver.check() == z3.sat:
            model = solver.model()
            return self._instantiate_template(danger_template, model)
        return None
        
    def _check_candidate_danger_invariant(self, candidate: z3.ExprRef) -> bool:
        """Check if candidate satisfies danger invariant conditions."""
        solver = z3.Solver()
        solver.set("timeout", min(5000, self.timeout * 100) if self.timeout else 5000)
        
        try:
            candidate_prime = z3.substitute(
                candidate,
                list(zip(list(self.sts.variables.values()), self.sts.prime_variables))
            )
            
            # Check inductiveness (essential)
            solver.push()
            solver.add(candidate, self.sts.trans, z3.Not(candidate_prime))
            if solver.check() == z3.sat:
                solver.pop()
                return False
            solver.pop()
            
            # Check satisfiability (essential)
            solver.push()
            solver.add(candidate)
            if solver.check() == z3.unsat:
                solver.pop()
                return False
            solver.pop()
            
            # Check error reachability (preferred but not essential)
            solver.push()
            solver.add(candidate, z3.Not(self.sts.post))
            error_reachable = solver.check() == z3.sat
            solver.pop()
            
            return error_reachable  # Prefer candidates that can reach errors
            
        except Exception:
            return False
            
    def _create_adaptive_template_variables(self, complexity: int) -> Dict[str, z3.ExprRef]:
        """Create template variables adaptively based on system and complexity."""
        template_vars = {}
        num_vars = len(self.sts.variables)
        max_coeffs = min(complexity, num_vars + 1)
        
        if self.sts.has_int:
            for i in range(max_coeffs):
                template_vars[f'c_{i}'] = z3.Int(f'c_{i}')
            if complexity > 1:
                for i in range(min(complexity - 1, num_vars)):
                    template_vars[f'lb_{i}'] = z3.Int(f'lb_{i}')
                    template_vars[f'ub_{i}'] = z3.Int(f'ub_{i}')
        elif self.sts.has_real:
            for i in range(max_coeffs):
                template_vars[f'c_{i}'] = z3.Real(f'c_{i}')
            if complexity > 1:
                for i in range(min(complexity - 1, num_vars)):
                    template_vars[f'lb_{i}'] = z3.Real(f'lb_{i}')
                    template_vars[f'ub_{i}'] = z3.Real(f'ub_{i}')
        elif self.sts.has_bv:
            bv_size = list(self.sts.variables.values())[0].sort().size()
            for i in range(max_coeffs):
                template_vars[f'c_{i}'] = z3.BitVec(f'c_{i}', bv_size)
            if complexity > 1:
                for i in range(min(complexity - 1, num_vars)):
                    template_vars[f'lb_{i}'] = z3.BitVec(f'lb_{i}', bv_size)
                    template_vars[f'ub_{i}'] = z3.BitVec(f'ub_{i}', bv_size)
        else:  # Boolean
            for i in range(min(complexity * 2, num_vars * 2)):
                template_vars[f'b_{i}'] = z3.Bool(f'b_{i}')
                
        return template_vars
        
    def _build_adaptive_template(self, template_vars: Dict[str, z3.ExprRef], complexity: int) -> z3.ExprRef:
        """Build danger invariant template adaptively."""
        if self.sts.has_bool:
            clauses = []
            var_list = list(self.sts.variables.values())
            for i, var in enumerate(var_list):
                if f'b_{i*2}' in template_vars:
                    clauses.append(z3.And(template_vars[f'b_{i*2}'], var))
                if f'b_{i*2+1}' in template_vars:
                    clauses.append(z3.And(template_vars[f'b_{i*2+1}'], z3.Not(var)))
            return z3.Or(*clauses) if clauses else z3.BoolVal(True)
        else:
            templates = []
            var_list = list(self.sts.variables.values())
            
            # Linear template (always include if coefficients exist)
            linear_terms = []
            if 'c_0' in template_vars:
                linear_terms.append(template_vars['c_0'])
            for i, var in enumerate(var_list):
                if f'c_{i+1}' in template_vars:
                    linear_terms.append(template_vars[f'c_{i+1}'] * var)
            if linear_terms:
                linear_expr = linear_terms[0] if len(linear_terms) == 1 else z3.Sum(*linear_terms)
                templates.append(linear_expr >= 0)
                if complexity > 2:  # Add negative version for higher complexity
                    templates.append(linear_expr <= 0)
            
            # Bound templates (include based on complexity)
            if complexity > 1:
                for i, var in enumerate(var_list):
                    if f'lb_{i}' in template_vars:
                        templates.append(var >= template_vars[f'lb_{i}'])
                    if f'ub_{i}' in template_vars:
                        templates.append(var <= template_vars[f'ub_{i}'])
            
            return z3.Or(*templates) if templates else z3.BoolVal(True)
            
    def _synthesize_ranking_function(self, danger_inv: z3.ExprRef) -> Optional[z3.ExprRef]:
        """Synthesize ranking function for danger invariant."""
        solver = z3.Solver()
        if self.timeout:
            solver.set("timeout", min(self.timeout * 1000, 30000))  # Cap at 30s
            
        # Try different ranking function complexities
        for complexity in range(1, min(self.template_complexity + 1, 4)):
            rank_vars = self._create_ranking_variables(complexity)
            rank_template = self._build_ranking_template(rank_vars)
            
            if self._try_ranking_synthesis(solver, danger_inv, rank_template, rank_vars):
                model = solver.model()
                return self._instantiate_ranking_template(rank_template, model)
                
        return None
        
    def _create_ranking_variables(self, complexity: int) -> Dict[str, z3.ExprRef]:
        """Create ranking function variables with adaptive complexity."""
        rank_vars = {}
        
        if self.sts.has_bool:
            for i in range(complexity):
                rank_vars[f'r_{i}'] = z3.Int(f'r_{i}')
        elif self.sts.has_int or self.sts.has_real:
            sort_fn = z3.Int if self.sts.has_int else z3.Real
            for i in range(complexity):
                rank_vars[f'r_{i}'] = sort_fn(f'r_{i}')
        elif self.sts.has_bv:
            bv_size = list(self.sts.variables.values())[0].sort().size()
            for i in range(complexity):
                rank_vars[f'r_{i}'] = z3.BitVec(f'r_{i}', bv_size)
                
        return rank_vars
        
    def _try_ranking_synthesis(self, solver: z3.Solver, danger_inv: z3.ExprRef, 
                              rank_template: z3.ExprRef, rank_vars: Dict[str, z3.ExprRef]) -> bool:
        """Try to synthesize ranking function with current template."""
        solver.push()
        
        try:
            rank_template_prime = z3.substitute(
                rank_template,
                list(zip(list(self.sts.variables.values()), self.sts.prime_variables))
            )
            
            # Add ranking constraints
            solver.add(z3.ForAll(list(self.sts.variables.values()),
                                z3.Implies(danger_inv, rank_template > 0)))
            solver.add(z3.ForAll(self.sts.all_variables,
                                z3.Implies(z3.And(danger_inv, self.sts.trans),
                                         rank_template_prime < rank_template)))
            
            return solver.check() == z3.sat
            
        except Exception:
            return False
        finally:
            solver.pop()
            
    def _check_initial_danger(self, danger_inv: z3.ExprRef) -> bool:
        """Check if initial state implies danger invariant (proves unsafety)."""
        solver = z3.Solver()
        solver.set("timeout", min(5000, self.timeout * 100) if self.timeout else 5000)
        
        try:
            solver.add(self.sts.init, z3.Not(danger_inv))
            return solver.check() == z3.unsat
        except Exception:
            return False
            
    def _build_ranking_template(self, template_vars: Dict[str, z3.ExprRef]) -> z3.ExprRef:
        """Build adaptive ranking function template."""
        terms = []
        if 'r_0' in template_vars:
            terms.append(template_vars['r_0'])
            
        var_list = list(self.sts.variables.values())
        for i, var in enumerate(var_list):
            if f'r_{i+1}' in template_vars:
                if self.sts.has_bool:
                    terms.append(template_vars[f'r_{i+1}'] * z3.If(var, 1, 0))
                else:
                    terms.append(template_vars[f'r_{i+1}'] * var)
                    
        if not terms:
            return z3.IntVal(1)  # Fallback constant
        return terms[0] if len(terms) == 1 else z3.Sum(*terms)
        
    def _verify_danger_invariant(self, danger_inv: z3.ExprRef, ranking_fn: Optional[z3.ExprRef]) -> bool:
        """Verify danger invariant properties with robust checking."""
        solver = z3.Solver()
        if self.timeout:
            solver.set("timeout", min(self.timeout * 1000, 60000))  # Cap at 1 minute
            
        try:
            danger_inv_prime = z3.substitute(
                danger_inv,
                list(zip(list(self.sts.variables.values()), self.sts.prime_variables))
            )
            
            # Check inductiveness (essential)
            solver.push()
            solver.add(danger_inv, self.sts.trans, z3.Not(danger_inv_prime))
            if solver.check() == z3.sat:
                solver.pop()
                return False
            solver.pop()
            
            # Check satisfiability (essential)
            solver.push()
            solver.add(danger_inv)
            if solver.check() == z3.unsat:
                solver.pop()
                return False
            solver.pop()
            
            # Verify ranking function if provided (optional)
            if ranking_fn is not None:
                if not self._verify_ranking_function(solver, danger_inv, ranking_fn):
                    logger.warning("Ranking function verification failed, proceeding without it")
                    self.ranking_function = None
                
            return True
            
        except Exception as e:
            logger.warning(f"Verification failed: {e}")
            return False
            
    def _verify_ranking_function(self, solver: z3.Solver, danger_inv: z3.ExprRef, ranking_fn: z3.ExprRef) -> bool:
        """Verify ranking function properties separately."""
        try:
            ranking_fn_prime = z3.substitute(
                ranking_fn,
                list(zip(list(self.sts.variables.values()), self.sts.prime_variables))
            )
            
            # Check bounded
            solver.push()
            solver.add(danger_inv, z3.Not(ranking_fn > 0))
            bounded = solver.check() == z3.unsat
            solver.pop()
            
            # Check decreasing
            solver.push()
            solver.add(danger_inv, self.sts.trans, z3.Not(ranking_fn_prime < ranking_fn))
            decreasing = solver.check() == z3.unsat
            solver.pop()
            
            return bounded and decreasing
            
        except Exception:
            return False
        
    def _instantiate_template(self, template: z3.ExprRef, model: z3.ModelRef) -> z3.ExprRef:
        """Instantiate template with model values."""
        substitutions = []
        for decl in model.decls():
            name = decl.name()
            if any(name.startswith(prefix) for prefix in ['c_', 'b_', 'lb_', 'ub_']):
                substitutions.append((decl(), model[decl]))
        return z3.substitute(template, substitutions)
        
    def _instantiate_ranking_template(self, template: z3.ExprRef, model: z3.ModelRef) -> z3.ExprRef:
        """Instantiate ranking template with model values."""
        substitutions = []
        for decl in model.decls():
            if decl.name().startswith('r_'):
                substitutions.append((decl(), model[decl]))
        return z3.substitute(template, substitutions)
        
    def get_statistics(self) -> Dict[str, Any]:
        """Get solving statistics."""
        return {
            'solve_time': self.solve_time,
            'iterations': self.iterations,
            'danger_invariant': str(self.danger_invariant) if self.danger_invariant else None,
            'ranking_function': str(self.ranking_function) if self.ranking_function else None,
            'has_ranking_function': self.ranking_function is not None
        }
