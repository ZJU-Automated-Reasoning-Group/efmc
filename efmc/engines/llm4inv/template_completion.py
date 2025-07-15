"""
Simplified Template Completion using SMT Solving

This module implements SMT-based template completion that fills holes in 
LLM-generated templates using exists-forall solving.
"""

import logging
import time
from typing import Dict, List, Optional, Tuple, Any
import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult, check_invariant
from efmc.utils.z3_expr_utils import extract_all
from efmc.engines.ef.efsmt.efsmt_solver import EFSMTSolver
from .template_dsl import TemplateInvariant, TemplateParser

logger = logging.getLogger(__name__)


class TemplateCompletion:
    """
    Template completion using SMT solving with optional trace support.
    
    This class takes templates with holes and uses SMT solving to find
    concrete values that make the template an inductive invariant.
    """
    
    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        self.bit_width = kwargs.get('bit_width', 32)
        self.solver = kwargs.get('solver', 'z3api')
        self.timeout = kwargs.get('timeout', 300)
        self.validate_result = kwargs.get('validate_result', True)
        self.max_traces = kwargs.get('max_traces', 10)
        
        # Initialize parser
        self.parser = TemplateParser(self.bit_width)
        var_dict = {str(var): var for var in self.sts.variables}
        self.parser.set_variables(var_dict)
        
        # Statistics
        self.completion_time = 0
        self.validation_time = 0
        
        # Initialize EFSMT solver if needed
        if self.solver == 'efsmt':
            self.efsmt_solver = EFSMTSolver(self.sts, timeout=self.timeout)
    
    def complete_template(self, template: TemplateInvariant, 
                         traces: List[Tuple[z3.ModelRef, z3.ModelRef]] = None) -> Optional[z3.ExprRef]:
        """
        Complete template by finding concrete values for holes.
        
        Args:
            template: Template with holes to complete
            traces: Optional execution traces for guidance
            
        Returns:
            Completed invariant or None if completion fails
        """
        start_time = time.time()
        
        try:
            # Convert template to Z3 expression
            template_expr, hole_vars = self.parser.template_to_z3(template)
            
            if not hole_vars:
                return template_expr
            
            # Generate verification conditions
            vc = self._generate_verification_conditions(template_expr, hole_vars)
            
            # Add trace constraints if provided
            if traces:
                trace_constraints = self._generate_trace_constraints(template_expr, traces)
                if trace_constraints:
                    vc = z3.And(vc, trace_constraints)
            
            # Solve for hole values
            if self.solver == 'z3api':
                result = self._solve_with_z3(vc, hole_vars)
            else:
                result = self._solve_with_efsmt(vc, hole_vars)
            
            if result.is_safe:
                invariant = self._build_invariant_from_model(result.model, template_expr, hole_vars)
                
                # Validate result if requested
                if self.validate_result:
                    validation_start = time.time()
                    is_valid = self._validate_invariant(invariant)
                    self.validation_time += time.time() - validation_start
                    
                    if not is_valid:
                        logger.warning("Template completion produced invalid invariant")
                        return None
                
                return invariant
            
            return None
            
        except Exception as e:
            logger.error(f"Template completion failed: {e}")
            return None
        finally:
            self.completion_time += time.time() - start_time
    
    def complete_multiple_templates(self, templates: List[TemplateInvariant], 
                                  traces: List[Tuple[z3.ModelRef, z3.ModelRef]] = None,
                                  max_attempts: int = 5) -> Optional[z3.ExprRef]:
        """
        Try to complete multiple templates and return the first successful one.
        
        Args:
            templates: List of templates to try
            traces: Optional execution traces for guidance
            max_attempts: Maximum number of templates to attempt
            
        Returns:
            First successfully completed invariant, or None if all fail
        """
        for i, template in enumerate(templates[:max_attempts]):
            logger.info(f"Attempting template completion {i+1}/{min(len(templates), max_attempts)}")
            
            result = self.complete_template(template, traces)
            if result is not None:
                logger.info(f"Template completion succeeded on attempt {i+1}")
                return result
        
        logger.info("All template completion attempts failed")
        return None
    
    def _generate_verification_conditions(self, template_expr: z3.ExprRef, 
                                        hole_vars: List[z3.ExprRef]) -> z3.ExprRef:
        """Generate verification conditions for template completion"""
        # Initiation: init(x) => T(x)
        init_vc = z3.Implies(self.sts.init, template_expr)
        
        # Consecution: T(x) ∧ trans(x, x') => T(x')
        template_prime = z3.substitute(template_expr, 
            [(var, prime_var) for var, prime_var in zip(self.sts.variables, self.sts.prime_variables)])
        
        cons_vc = z3.Implies(
            z3.And(template_expr, self.sts.trans),
            template_prime
        )
        
        # Safety: T(x) => post(x)
        safety_vc = z3.Implies(template_expr, self.sts.post)
        
        return z3.And(init_vc, cons_vc, safety_vc)
    
    def _generate_trace_constraints(self, template_expr: z3.ExprRef, 
                                  traces: List[Tuple[z3.ModelRef, z3.ModelRef]]) -> Optional[z3.ExprRef]:
        """Generate constraints based on execution traces"""
        if not traces:
            return None
        
        constraints = []
        
        for i, (pre_state, post_state) in enumerate(traces[:self.max_traces]):
            # Create substitutions for trace states
            pre_subs = [(var, pre_state[var]) for var in self.sts.variables if var in pre_state]
            post_subs = [(var, post_state[var]) for var in self.sts.variables if var in post_state]
            
            # Template should hold at reachable pre-states
            if pre_subs:
                template_at_pre = z3.substitute(template_expr, pre_subs)
                constraints.append(template_at_pre)
            
            # Template should be preserved by transition
            if pre_subs and post_subs:
                template_at_post = z3.substitute(template_expr, post_subs)
                constraints.append(z3.Implies(template_at_pre, template_at_post))
        
        return z3.And(constraints) if constraints else None
    
    def _solve_with_z3(self, vc: z3.ExprRef, hole_vars: List[z3.ExprRef]) -> VerificationResult:
        """Solve verification conditions using Z3"""
        solver = z3.Solver()
        solver.set("timeout", self.timeout * 1000)
        
        # Add the verification conditions
        solver.add(vc)
        
        # Check satisfiability
        result = solver.check()
        
        if result == z3.sat:
            model = solver.model()
            return VerificationResult(True, model=model)
        elif result == z3.unsat:
            return VerificationResult(False, reason="Verification conditions unsatisfiable")
        else:
            return VerificationResult(False, reason="Timeout or unknown")
    
    def _solve_with_efsmt(self, vc: z3.ExprRef, hole_vars: List[z3.ExprRef]) -> VerificationResult:
        """Solve verification conditions using EFSMT"""
        try:
            result = self.efsmt_solver.solve_exists_forall(vc, hole_vars)
            return result
        except Exception as e:
            logger.error(f"EFSMT solving failed: {e}")
            return VerificationResult(False, reason=f"EFSMT error: {e}")
    
    def _build_invariant_from_model(self, model: z3.ModelRef, template_expr: z3.ExprRef, 
                                   hole_vars: List[z3.ExprRef]) -> z3.ExprRef:
        """Build concrete invariant from model by substituting hole values"""
        if not model or not hole_vars:
            return template_expr
        
        # Create substitution map from holes to concrete values
        substitutions = []
        for hole_var in hole_vars:
            if model[hole_var] is not None:
                substitutions.append((hole_var, model[hole_var]))
        
        # Apply substitutions to get concrete invariant
        return z3.substitute(template_expr, substitutions)
    
    def _validate_invariant(self, invariant: z3.ExprRef) -> bool:
        """Validate that the invariant is actually inductive"""
        # Create primed version of invariant
        var_map = [(var, prime_var) for var, prime_var in zip(self.sts.variables, self.sts.prime_variables)]
        invariant_prime = z3.substitute(invariant, var_map)
        
        return check_invariant(self.sts, invariant, invariant_prime)
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get completion statistics"""
        return {
            'completion_time': self.completion_time,
            'validation_time': self.validation_time,
            'total_time': self.completion_time + self.validation_time
        } 