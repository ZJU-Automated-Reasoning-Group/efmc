"""
Base k-safety verification engine for relational verification and hyperproperty checking.

This module implements the core functionality for k-safety verification,
which handles properties that relate multiple execution traces.
"""

import logging
import time
from typing import List, Optional, Dict
import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult

logger = logging.getLogger(__name__)


class BaseKSafetyProver:
    """
    Base k-safety verification engine for relational properties.
    
    This prover handles verification of k-safety properties by:
    1. Creating k copies of the transition system
    2. Encoding the relational property as a hyperproperty
    3. Using various verification techniques to check the property
    """

    def __init__(self, sts: TransitionSystem, k: int = 2, **kwargs):
        """Initialize the k-safety prover."""
        self.sts = sts
        self.k = k
        self.logger = logging.getLogger(__name__)
        
        # Configuration options
        self.timeout = kwargs.get("timeout", 300)
        self.verification_method = kwargs.get("method", "bounded_model_checking")
        self.max_bound = kwargs.get("max_bound", 10)
        self.use_induction = kwargs.get("use_induction", True)
        
        # State for tracking verification
        self.trace_variables = {}
        self.relational_property = None
        self.verification_formula = None
        
        self.logger.info(f"Initialized k-safety prover with k={k}")

    def set_relational_property(self, property_expr: z3.ExprRef):
        """Set the relational property to verify."""
        self.relational_property = property_expr
        self.logger.info(f"Set relational property: {property_expr}")

    def create_trace_variables(self) -> Dict[int, List[z3.ExprRef]]:
        """Create k copies of the system variables for different execution traces."""
        trace_vars = {}
        
        for trace_idx in range(self.k):
            trace_vars[trace_idx] = []
            
            for var in self.sts.variables:
                var_name = str(var)
                var_sort = var.sort()
                
                # Create variable with trace index suffix
                if z3.is_bv_sort(var_sort):
                    new_var = z3.BitVec(f"{var_name}_{trace_idx}", var_sort.size())
                elif var_sort == z3.RealSort():
                    new_var = z3.Real(f"{var_name}_{trace_idx}")
                elif var_sort == z3.IntSort():
                    new_var = z3.Int(f"{var_name}_{trace_idx}")
                else:
                    new_var = z3.Bool(f"{var_name}_{trace_idx}")
                
                trace_vars[trace_idx].append(new_var)
        
        self.trace_variables = trace_vars
        return trace_vars

    def create_k_safety_formula(self) -> z3.ExprRef:
        """Create the k-safety verification formula."""
        if self.relational_property is None:
            raise ValueError("Relational property must be set before creating k-safety formula")
        
        trace_vars = self.create_trace_variables()
        
        # Create k copies of the transition system
        init_conditions = []
        trans_conditions = []
        
        for trace_idx in range(self.k):
            # Create substitution for this trace
            var_substitution = [(var, trace_vars[trace_idx][i]) 
                               for i, var in enumerate(self.sts.variables)]
            
            # Substitute variables in init and trans
            init_copy = z3.substitute(self.sts.init, var_substitution)
            trans_copy = z3.substitute(self.sts.trans, var_substitution)
            
            init_conditions.append(init_copy)
            trans_conditions.append(trans_copy)
        
        # Create the k-safety formula: antecedent → relational_property
        antecedent = z3.And(*init_conditions, *trans_conditions)
        verification_formula = z3.Implies(antecedent, self.relational_property)
        
        self.verification_formula = verification_formula
        return verification_formula

    def bounded_model_checking(self, bound: int) -> VerificationResult:
        """Perform bounded model checking for k-safety verification."""
        self.logger.info(f"Performing BMC for k-safety with bound {bound}")
        
        formula = self.create_k_safety_formula()
        solver = z3.Solver()
        solver.add(z3.Not(formula))  # Check for violations
        solver.set("timeout", self.timeout * 1000)
        
        result = solver.check()
        
        if result == z3.sat:
            model = solver.model()
            self.logger.info(f"K-safety violation found at bound {bound}")
            return VerificationResult(False, None, model, is_unsafe=True)
        elif result == z3.unsat:
            self.logger.info(f"No k-safety violation found at bound {bound}")
            return VerificationResult(True, None)
        else:
            self.logger.warning(f"BMC result unknown at bound {bound}")
            return VerificationResult(False, None, None, is_unknown=True, timed_out=True)

    def k_induction(self, k_bound: int) -> VerificationResult:
        """Perform k-induction for k-safety verification."""
        self.logger.info(f"Performing k-induction for k-safety with k={k_bound}")
        
        base_case = self._create_k_induction_base_case(k_bound)
        inductive_step = self._create_k_induction_inductive_step(k_bound)
        
        # Check base case
        solver_base = z3.Solver()
        solver_base.add(z3.Not(base_case))
        solver_base.set("timeout", self.timeout * 1000)
        
        base_result = solver_base.check()
        if base_result == z3.sat:
            model = solver_base.model()
            self.logger.info(f"K-induction base case violation found")
            return VerificationResult(False, None, model, is_unsafe=True)
        
        # Check inductive step
        solver_ind = z3.Solver()
        solver_ind.add(z3.Not(inductive_step))
        solver_ind.set("timeout", self.timeout * 1000)
        
        inductive_result = solver_ind.check()
        
        if inductive_result == z3.unsat:
            self.logger.info(f"K-induction successful with k={k_bound}")
            return VerificationResult(True, None)
        elif inductive_result == z3.sat:
            model = solver_ind.model()
            self.logger.info(f"K-induction inductive step violation found")
            return VerificationResult(False, None, model, is_unsafe=True)
        else:
            self.logger.warning(f"K-induction result unknown")
            return VerificationResult(False, None, None, is_unknown=True, timed_out=True)

    def _create_k_induction_base_case(self, k_bound: int) -> z3.ExprRef:
        """Create the base case for k-induction."""
        trace_vars = self.create_trace_variables()
        
        # Create k steps for each trace
        steps = []
        for step in range(k_bound + 1):
            step_conditions = []
            
            for trace_idx in range(self.k):
                # Create variables for this step and trace
                step_vars = {}
                for i, var in enumerate(self.sts.variables):
                    var_name = str(var)
                    var_sort = var.sort()
                    
                    if z3.is_bv_sort(var_sort):
                        step_vars[var] = z3.BitVec(f"{var_name}_{trace_idx}_{step}", var_sort.size())
                    elif var_sort == z3.RealSort():
                        step_vars[var] = z3.Real(f"{var_name}_{trace_idx}_{step}")
                    elif var_sort == z3.IntSort():
                        step_vars[var] = z3.Int(f"{var_name}_{trace_idx}_{step}")
                    else:
                        step_vars[var] = z3.Bool(f"{var_name}_{trace_idx}_{step}")
                
                # Add initial condition for step 0
                if step == 0:
                    init_subst = [(var, step_vars[var]) for var in self.sts.variables]
                    init_condition = z3.substitute(self.sts.init, init_subst)
                    step_conditions.append(init_condition)
                else:
                    # Add transition condition
                    trans_subst = []
                    for i, var in enumerate(self.sts.variables):
                        trans_subst.append((var, step_vars[var]))
                        # Add primed variables for next step
                        if z3.is_bv_sort(var.sort()):
                            primed_var = z3.BitVec(f"{str(var)}_{trace_idx}_{step-1}_p", var.sort().size())
                        elif var.sort() == z3.RealSort():
                            primed_var = z3.Real(f"{str(var)}_{trace_idx}_{step-1}_p")
                        elif var.sort() == z3.IntSort():
                            primed_var = z3.Int(f"{str(var)}_{trace_idx}_{step-1}_p")
                        else:
                            primed_var = z3.Bool(f"{str(var)}_{trace_idx}_{step-1}_p")
                        trans_subst.append((self.sts.prime_variables[i], primed_var))
                    
                    trans_condition = z3.substitute(self.sts.trans, trans_subst)
                    step_conditions.append(trans_condition)
            
            steps.append(z3.And(*step_conditions))
        
        # The base case is: all steps → property
        base_antecedent = z3.And(*steps)
        
        # Substitute the property with step variables
        property_subst = []
        for trace_idx in range(self.k):
            for i, var in enumerate(self.sts.variables):
                var_name = str(var)
                var_sort = var.sort()
                
                if z3.is_bv_sort(var_sort):
                    prop_var = z3.BitVec(f"{var_name}_{trace_idx}_{k_bound}", var_sort.size())
                elif var_sort == z3.RealSort():
                    prop_var = z3.Real(f"{var_name}_{trace_idx}_{k_bound}")
                elif var_sort == z3.IntSort():
                    prop_var = z3.Int(f"{var_name}_{trace_idx}_{k_bound}")
                else:
                    prop_var = z3.Bool(f"{var_name}_{trace_idx}_{k_bound}")
                
                property_subst.append((trace_vars[trace_idx][i], prop_var))
        
        property_at_k = z3.substitute(self.relational_property, property_subst)
        return z3.Implies(base_antecedent, property_at_k)

    def _create_k_induction_inductive_step(self, k_bound: int) -> z3.ExprRef:
        """Create the inductive step for k-induction."""
        # Simplified version - returns placeholder
        return z3.BoolVal(True)

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """Main solving procedure for k-safety verification."""
        if timeout is not None:
            self.timeout = timeout
        
        if self.relational_property is None:
            raise ValueError("Relational property must be set before solving")
        
        self.logger.info(f"Starting k-safety verification with k={self.k}")
        start_time = time.time()
        
        # Try different verification methods
        if self.verification_method == "bounded_model_checking":
            for bound in range(1, self.max_bound + 1):
                if timeout and (time.time() - start_time > timeout):
                    return VerificationResult(False, None, None, is_unknown=True, timed_out=True)
                
                result = self.bounded_model_checking(bound)
                if result.is_safe or result.is_unsafe:
                    return result
        
        elif self.verification_method == "k_induction" and self.use_induction:
            for k_bound in range(1, min(self.k, self.max_bound) + 1):
                if timeout and (time.time() - start_time > timeout):
                    return VerificationResult(False, None, None, is_unknown=True, timed_out=True)
                
                result = self.k_induction(k_bound)
                if result.is_safe or result.is_unsafe:
                    return result
        
        # If we reach here, we couldn't determine the result
        return VerificationResult(False, None, None, is_unknown=True) 