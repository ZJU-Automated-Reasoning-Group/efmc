"""
Termination prover using ranking function templates for bit-vector programs.

This module implements a template-based approach to termination verification
using ranking functions. It extends the EF prover to synthesize ranking functions
that prove program termination.

For a loop with guard G and body B, termination is proven by finding a ranking
function R such that:
1. R(x) >= 0 for all states x where G(x) holds (non-negativity)
2. For all states x where G(x) holds, if B(x, x'), then R(x) > R(x') (decrease)
3. The ranking function is well-founded (bounded below)
"""

import logging
import time
from typing import List, Dict, Any, Optional, Union, Tuple

import z3

from efmc.sts import TransitionSystem
from efmc.utils import is_entail
from efmc.utils.bv_utils import Signedness
from efmc.engines.ef.templates import *
from efmc.engines.ef.efsmt.efsmt_solver import EFSMTSolver
from efmc.utils.z3_expr_utils import extract_all, ctx_simplify, big_and
from efmc.utils.verification_utils import VerificationResult, check_invariant

logger = logging.getLogger(__name__)


class TerminationResult:
    """
    Simple result class for termination verification.
    """
    def __init__(self, result: bool, time: float = 0.0, error: str = None):
        self.result = result
        self.time = time
        self.error = error


class TerminationProver:
    """
    Template-based termination verification using ranking function synthesis.
    
    This class implements termination verification for bit-vector programs by
    synthesizing ranking functions that prove the program terminates.
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        self.ranking_template = None
        self.logic = "BV"  # Default to bit-vector logic
        self.ranking_function = None  # The synthesized ranking function
        self.print_vc = kwargs.get("print_vc", False)
        
        # Configuration options
        self.seed = kwargs.get("seed", 1)
        self.solver = kwargs.get("solver", "z3api")
        self.validate_ranking_function = kwargs.get("validate_ranking_function", False)
        self.pysmt_solver = kwargs.get("pysmt_solver", "z3")
        
        # Template-specific options
        self.num_components = kwargs.get("num_components", 2)  # For lexicographic
        self.num_branches = kwargs.get("num_branches", 2)     # For conditional

    def set_ranking_template(self, template_name: str, **kwargs):
        """Set the ranking function template to use."""
        if not self.sts.has_bv:
            raise NotImplementedError("Currently only bit-vector programs are supported")
            
        template_map = {
            "bv_linear_ranking": BitVecLinearRankingTemplate,
            "bv_lexicographic_ranking": lambda sts, **kw: BitVecLexicographicRankingTemplate(
                sts, num_components=self.num_components, **kw
            ),
            "bv_conditional_ranking": lambda sts, **kw: BitVecConditionalRankingTemplate(
                sts, num_branches=self.num_branches, **kw
            )
        }
        
        if template_name not in template_map:
            raise NotImplementedError(f"Ranking template '{template_name}' not implemented")
            
        self.ranking_template = template_map[template_name](self.sts, **kwargs)

    def prove_termination(self, timeout: Optional[int] = None) -> TerminationResult:
        """
        Prove termination by synthesizing a ranking function.
        
        Returns:
            TerminationResult indicating whether termination was proven
        """
        if self.ranking_template is None:
            raise ValueError("No ranking template set. Call set_ranking_template() first.")
            
        start_time = time.time()
        
        try:
            # Generate verification condition for ranking function
            vc = self.generate_ranking_vc()
            
            if self.print_vc:
                print("Ranking function verification condition:")
                print(vc)
            
            # Solve the verification condition
            result = self.solve_ranking_vc(vc, timeout)
            
            end_time = time.time()
            result.time = end_time - start_time
            
            return result
            
        except Exception as e:
            logger.error(f"Error in termination proving: {e}")
            return TerminationResult(
                result=False,
                time=time.time() - start_time,
                error=str(e)
            )

    def generate_ranking_vc(self) -> z3.ExprRef:
        """
        Generate verification condition for ranking function synthesis.
        
        The VC ensures:
        1. Non-negativity: guard(x) => R(x) >= 0
        2. Decrease: guard(x) ∧ trans(x, x') => R(x) > R(x')
        3. Well-foundedness: R(x) is bounded below
        """
        constraints = []
        
        # Get template variables
        template_vars = extract_all(self.ranking_template.template_vars)
        if hasattr(self.ranking_template, 'condition_vars'):
            template_vars.extend(self.ranking_template.condition_vars)
        
        # Build ranking function expressions
        rank_current, rank_next = self._build_ranking_expressions()
        
        # Extract guard from transition relation
        guard = self.sts.trans if self.sts.trans is not None else z3.BoolVal(True)
        
        # 1. Non-negativity constraint: guard(x) => R(x) >= 0
        if self.ranking_template.signedness == Signedness.UNSIGNED:
            # For unsigned bit-vectors, non-negativity is automatic
            non_neg_constraint = z3.BoolVal(True)
        else:
            # For signed bit-vectors, explicitly require >= 0
            non_neg_constraint = z3.Implies(guard, rank_current >= 0)
        
        constraints.append(non_neg_constraint)
        
        # 2. Decrease constraint: guard(x) ∧ trans(x, x') => R(x) > R(x')
        trans_constraint = self.sts.trans if self.sts.trans is not None else z3.BoolVal(True)
        
        if self.ranking_template.signedness == Signedness.UNSIGNED:
            decrease_constraint = z3.Implies(trans_constraint, z3.UGT(rank_current, rank_next))
        else:
            decrease_constraint = z3.Implies(trans_constraint, rank_current > rank_next)
            
        constraints.append(decrease_constraint)
        
        # 3. Well-foundedness constraint (ranking function is bounded below)
        # For bit-vectors, this is automatically satisfied due to finite domain
        
        # 4. Initial state constraint (if applicable)
        if self.sts.init is not None and self.ranking_template.signedness != Signedness.UNSIGNED:
            init_constraint = z3.Implies(self.sts.init, rank_current >= 0)
            constraints.append(init_constraint)
        
        # Combine all constraints
        vc = big_and(constraints)
        
        # Add template-specific constraints
        for attr in ['template_cnt_init_and_post', 'template_cnt_trans']:
            if hasattr(self.ranking_template, attr):
                vc = z3.And(vc, getattr(self.ranking_template, attr))
        
        return vc

    def _build_ranking_expressions(self) -> Tuple[z3.ExprRef, z3.ExprRef]:
        """Build ranking function expressions for current and next states."""
        # Try different methods to build ranking expressions
        build_methods = [
            '_build_ranking_expr',
            '_build_conditional_ranking_expr',
            'build_invariant_expr'
        ]
        
        for method_name in build_methods:
            if hasattr(self.ranking_template, method_name):
                method = getattr(self.ranking_template, method_name)
                if method_name == 'build_invariant_expr':
                    # Special handling for build_invariant_expr
                    dummy_model = self._create_dummy_model()
                    if dummy_model:
                        rank_current = method(dummy_model, use_prime_variables=False)
                        rank_next = method(dummy_model, use_prime_variables=True)
                        return rank_current, rank_next
                else:
                    rank_current = method(self.sts.variables)
                    rank_next = method(self.sts.prime_variables)
                    return rank_current, rank_next
        
        # Fallback to simple expressions
        return z3.BitVecVal(0, 32), z3.BitVecVal(0, 32)

    def solve_ranking_vc(self, vc: z3.ExprRef, timeout: Optional[int] = None) -> TerminationResult:
        """Solve the ranking function verification condition."""
        # Get template variables for existential quantification
        exists_vars = extract_all(self.ranking_template.template_vars)
        if hasattr(self.ranking_template, 'condition_vars'):
            exists_vars.extend(self.ranking_template.condition_vars)
        
        # Get program variables for universal quantification
        forall_vars = self.sts.all_variables
        
        # Create EF solver
        ef_solver = EFSMTSolver(logic=self.logic, solver=self.solver)
        ef_solver.init(exist_vars=exists_vars, forall_vars=forall_vars, phi=vc)
        
        # For z3api solver, we can handle timeout by modifying the solver directly
        if self.solver == "z3api" and timeout:
            # We'll need to modify the solve method to handle timeout
            # For now, let's use a simpler approach with direct Z3 solving
            return self._solve_with_z3_timeout(vc, exists_vars, forall_vars, timeout)
        
        # Solve without timeout for other solvers
        try:
            result = ef_solver.solve()
            
            if result == "sat":
                # Extract ranking function from model
                # For now, we'll create a simple model extraction
                # This is a simplified approach - in practice you'd need proper model extraction
                self.ranking_function = self.ranking_template.build_invariant_expr(
                    self._create_dummy_model(), use_prime_variables=False
                )
                    
                if self.validate_ranking_function and not self._validate_ranking_function():
                    logger.warning("Synthesized ranking function failed validation")
                    return TerminationResult(
                        result=False,
                        error="Ranking function validation failed"
                    )
                
                return TerminationResult(result=True)
            else:
                return TerminationResult(
                    result=False,
                    error=f"Could not find ranking function: {result}"
                )
                
        except Exception as e:
            logger.error(f"Error in EF solver: {e}")
            return TerminationResult(
                result=False,
                error=f"Solver error: {e}"
            )

    def _solve_with_z3_timeout(self, vc: z3.ExprRef, exists_vars, forall_vars, timeout: int) -> TerminationResult:
        """Solve with Z3 directly using timeout."""
        try:
            # Create Z3 solver with timeout
            solver = z3.Solver()
            solver.set("timeout", timeout * 1000)  # Z3 timeout is in milliseconds
            
            # Create quantified formula: ForAll forall_vars. vc
            if forall_vars:
                quantified_formula = z3.ForAll(forall_vars, vc)
            else:
                quantified_formula = vc
                
            solver.add(quantified_formula)
            
            # Check satisfiability
            result = solver.check()
            
            if result == z3.sat:
                # Extract model and build ranking function
                model = solver.model()
                self.ranking_function = self.ranking_template.build_invariant_expr(
                    model, use_prime_variables=False
                )
                
                if self.validate_ranking_function and not self._validate_ranking_function():
                    logger.warning("Synthesized ranking function failed validation")
                    return TerminationResult(
                        result=False,
                        error="Ranking function validation failed"
                    )
                
                return TerminationResult(result=True)
            elif result == z3.unsat:
                return TerminationResult(
                    result=False,
                    error="No ranking function exists"
                )
            else:  # unknown
                return TerminationResult(
                    result=False,
                    error="Solver timeout or unknown result"
                )
                
        except Exception as e:
            logger.error(f"Error in Z3 solver: {e}")
            return TerminationResult(
                result=False,
                error=f"Z3 solver error: {e}"
            )

    def _create_dummy_model(self) -> z3.ModelRef:
        """Create a dummy model for testing purposes."""
        solver = z3.Solver()
        solver.add(z3.BoolVal(True))
        if solver.check() == z3.sat:
            return solver.model()
        else:
            # Fallback: create an empty model-like object
            # This is not ideal but allows basic functionality
            return None

    def _validate_ranking_function(self) -> bool:
        """
        Validate that the synthesized ranking function is correct.
        
        Returns:
            True if the ranking function is valid, False otherwise
        """
        if self.ranking_function is None:
            return False
            
        # Create solver for validation
        solver = z3.Solver()
        
        # Check non-negativity
        if self.ranking_template.signedness == Signedness.SIGNED:
            # For signed bit-vectors, check that R(x) >= 0 when guard holds
            if self.sts.trans:
                non_neg_check = z3.Implies(self.sts.trans, self.ranking_function >= 0)
            else:
                non_neg_check = self.ranking_function >= 0
                
            solver.push()
            solver.add(z3.Not(non_neg_check))
            if solver.check() == z3.sat:
                logger.warning("Ranking function non-negativity validation failed")
                solver.pop()
                return False
            solver.pop()
        
        # Check decrease property
        rank_next = z3.substitute(
            self.ranking_function,
            [(v, v_prime) for v, v_prime in zip(self.sts.variables, self.sts.prime_variables)]
        )
        
        if self.sts.trans:
            if self.ranking_template.signedness == Signedness.UNSIGNED:
                decrease_check = z3.Implies(self.sts.trans, z3.UGT(self.ranking_function, rank_next))
            else:
                decrease_check = z3.Implies(self.sts.trans, self.ranking_function > rank_next)
        else:
            if self.ranking_template.signedness == Signedness.UNSIGNED:
                decrease_check = z3.UGT(self.ranking_function, rank_next)
            else:
                decrease_check = self.ranking_function > rank_next
        
        solver.push()
        solver.add(z3.Not(decrease_check))
        if solver.check() == z3.sat:
            logger.warning("Ranking function decrease validation failed")
            solver.pop()
            return False
        solver.pop()
        
        return True

    def get_ranking_function(self) -> Optional[z3.ExprRef]:
        """Get the synthesized ranking function."""
        return self.ranking_function

    def get_ranking_function_components(self) -> Optional[List[z3.ExprRef]]:
        """
        Get all components of a lexicographic ranking function.
        
        Returns:
            List of ranking function components, or None if not lexicographic
        """
        if (isinstance(self.ranking_template, BitVecLexicographicRankingTemplate) and 
            hasattr(self.ranking_template, 'build_lexicographic_ranking_function')):
            # Need to get the model first
            # This is a simplified version - in practice you'd store the model
            return None  # TODO: Implement proper model storage and retrieval
        return None

    def dump_ranking_function(self, filename: str) -> None:
        """Dump the synthesized ranking function to a file."""
        if self.ranking_function is None:
            logger.warning("No ranking function to dump")
            return
            
        with open(filename, 'w') as f:
            f.write(f"Ranking function: {self.ranking_function}\n")
            f.write(f"Simplified: {z3.simplify(self.ranking_function)}\n")
            
            # If lexicographic, dump all components
            components = self.get_ranking_function_components()
            if components:
                f.write("Lexicographic components:\n")
                for i, comp in enumerate(components):
                    f.write(f"  Component {i}: {comp}\n")
                    f.write(f"  Simplified {i}: {z3.simplify(comp)}\n")


def prove_termination_with_ranking_functions(sts: TransitionSystem, 
                                              template_names: List[str] = None,
                                              timeout: Optional[int] = None,
                                              **kwargs) -> Tuple[bool, Optional[z3.ExprRef], str]:
    """
    Convenience function to prove termination using various ranking function templates.
    
    Args:
        sts: Transition system to analyze
        template_names: List of template names to try (default: all available)
        timeout: Timeout in seconds
        **kwargs: Additional options
        
    Returns:
        Tuple of (success, ranking_function, template_used)
    """
    if template_names is None:
        template_names = [
            "bv_linear_ranking",
            "bv_lexicographic_ranking", 
            "bv_conditional_ranking"
        ]
    
    for template_name in template_names:
        logger.info(f"Trying ranking template: {template_name}")
        
        try:
            prover = TerminationProver(sts, **kwargs)
            prover.set_ranking_template(template_name, **kwargs)
            
            result = prover.prove_termination(timeout=timeout)
            
            if result.result:
                logger.info(f"Termination proven with template: {template_name}")
                return True, prover.get_ranking_function(), template_name
                
        except Exception as e:
            logger.warning(f"Template {template_name} failed: {e}")
            continue
    
    logger.info("Could not prove termination with any template")
    return False, None, "" 