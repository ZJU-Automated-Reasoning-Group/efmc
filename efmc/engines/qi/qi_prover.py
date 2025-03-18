"""
Encode the verification problem as a quantified formula and use
SMT solvers that support quantifiers
- E-matching
- MBQI (model-based quantifier instantiation)
- Enumerative instantiation in CVC5

Configuration z3y
- MBQI: auto_config=false smt.ematching=false
- E-matching: auto_config=false smt.mbqi=false
- M+E is enabled by default

Configuration CVC5
- E-matching
- CEGQI
- ...

Currently, only Z3 is supported.
"""

import logging
import time
from typing import Optional, Dict, Any, Tuple

import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult

logger = logging.getLogger(__name__)


class QuantifierInstantiationProver:
    def __init__(self, system: TransitionSystem, **kwargs):
        """
        Initialize the Quantifier Instantiation prover.
        
        Args:
            system: The transition system to verify
            **kwargs: Additional configuration options
                - timeout: Maximum solving time in seconds
                - qi_strategy: QI strategy to use ('mbqi', 'ematching', 'combined', or 'auto')
                - verbose: Whether to print detailed information
        """
        self.sts = system
        self.timeout = kwargs.get('timeout', None)
        self.qi_strategy = kwargs.get('qi_strategy', 'auto')
        self.verbose = kwargs.get('verbose', True)
        self.invariant = None

    def _create_inv_function(self) -> z3.FuncDeclRef:
        """
        Create the uninterpreted 'inv' function with appropriate signature.
        
        Returns:
            The inv function declaration
        """
        # Build argument types based on variable types
        arg_sorts = []

        if self.sts.has_int:
            arg_sorts = [z3.IntSort() for _ in range(len(self.sts.variables))]
        elif self.sts.has_real:
            arg_sorts = [z3.RealSort() for _ in range(len(self.sts.variables))]
        elif self.sts.has_bv:
            bv_size = self.sts.variables[0].sort().size()
            arg_sorts = [z3.BitVecSort(bv_size) for _ in range(len(self.sts.variables))]
        else:
            raise NotImplementedError("Unsupported variable types in transition system")

        # Create the function
        return z3.Function('inv', *(arg_sorts + [z3.BoolSort()]))

    def _configure_solver(self) -> z3.Solver:
        """
        Configure the solver based on the transition system and QI strategy.
        
        Returns:
            Configured Z3 solver
        """
        # Select appropriate logic
        if self.sts.has_int:
            s = z3.SolverFor("UFLIA")
        elif self.sts.has_real:
            s = z3.SolverFor("AUFLIRA")
        elif self.sts.has_bv:
            s = z3.SolverFor("UFBV")
        else:
            raise NotImplementedError("Unsupported variable types in transition system")

        # Configure QI strategy
        if self.qi_strategy == 'mbqi':
            s.set('auto_config', False)
            s.set('smt.ematching', False)
            s.set('smt.mbqi', True)
        elif self.qi_strategy == 'ematching':
            s.set('auto_config', False)
            s.set('smt.mbqi', False)
            s.set('smt.ematching', True)
        elif self.qi_strategy == 'combined':
            s.set('auto_config', False)
            s.set('smt.mbqi', True)
            s.set('smt.ematching', True)
        # For 'auto', use Z3's default configuration

        # Set timeout if specified
        if self.timeout:
            s.set('timeout', self.timeout * 1000)  # Z3 timeout is in milliseconds

        return s

    def encode_verification_conditions(self, inv: z3.FuncDeclRef, solver: z3.Solver) -> None:
        """
        Encode the verification conditions using the inv function.
        
        Args:
            inv: The invariant function
            solver: The Z3 solver to add constraints to
        """
        # Encode initiation condition: init(X) => inv(X)
        solver.add(z3.ForAll(self.sts.variables,
                             z3.Implies(self.sts.init, inv(*self.sts.variables))))

        # Encode consecution condition: inv(X) ∧ trans(X,X') => inv(X')
        solver.add(z3.ForAll(self.sts.all_variables,
                             z3.Implies(z3.And(inv(*self.sts.variables), self.sts.trans),
                                        inv(*self.sts.prime_variables))))

        # Encode safety condition: inv(X) => post(X)
        solver.add(z3.ForAll(self.sts.variables,
                             z3.Implies(inv(*self.sts.variables), self.sts.post)))

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """
        Verify the transition system using quantifier instantiation.
        
        Returns:
            VerificationResult: Object containing verification result and related data
        """
        assert self.sts.initialized, "Transition system must be initialized before solving"

        try:
            # Create invariant function and configure solver
            inv = self._create_inv_function()
            solver = self._configure_solver()

            # Set timeout if specified
            if timeout is not None:
                solver.set("timeout", timeout * 1000)  # Z3 timeout is in milliseconds

            # Encode verification conditions
            self.encode_verification_conditions(inv, solver)

            if self.verbose:
                logger.info("QI starting with strategy: %s", self.qi_strategy)

            # Solve the verification problem
            start_time = time.time()
            result = solver.check()
            solve_time = time.time() - start_time

            if result == z3.sat:
                # System is safe, extract invariant
                model = solver.model()
                self.invariant = model.eval(inv(*self.sts.variables))

                if self.verbose:
                    logger.info("QI succeeded in %.2f seconds", solve_time)
                    logger.info("Invariant: %s", self.invariant)

                return VerificationResult(True, self.invariant)

            elif result == z3.unsat:
                if self.verbose:
                    logger.info("QI found property violation in %.2f seconds", solve_time)

                # We don't have a specific counterexample, so we mark it as unknown
                # rather than unsafe since we can't provide a concrete counterexample
                return VerificationResult(False, None, None, is_unknown=True)

            else:
                if self.verbose:
                    logger.warning("QI returned unknown result after %.2f seconds", solve_time)
                    logger.warning("Reason: %s", solver.reason_unknown())
                
                if timeout is not None and time.time() - start_time >= timeout:
                    logger.info("Timeout reached after %d seconds", timeout)
                    return VerificationResult(False, None, None, is_timeout=True, is_unknown=True)

                return VerificationResult(False, None, None, is_unknown=True)

        except z3.Z3Exception as e:
            logger.error("Z3 error during QI solving: %s", str(e))
            return VerificationResult(False, None, None, is_unknown=True)

        except Exception as e:
            logger.error("Unexpected error during QI solving: %s", str(e))
            return VerificationResult(False, None, None, is_unknown=True)

    def get_invariant(self) -> Optional[z3.ExprRef]:
        """
        Get the inductive invariant found during verification.
        
        Returns:
            The invariant expression if found, None otherwise
        """
        return self.invariant

    def try_multiple_strategies(self) -> VerificationResult:
        """
        Try multiple QI strategies and return the best result.
        
        Returns:
            VerificationResult: Object containing verification result and related data
        """
        strategies = ['mbqi', 'ematching', 'combined']
        best_result = VerificationResult(False, None, None, is_unknown=True)

        for strategy in strategies:
            logger.info("Trying QI strategy: %s", strategy)
            self.qi_strategy = strategy
            result = self.solve()

            if result.is_safe:
                return result

            # Keep the best result (prefer unsafe over unknown)
            if result.is_unsafe:
                best_result = result
                break  # If we found a counterexample, no need to try other strategies

        return best_result

    def set_strategy(self, strategy: str) -> None:
        """
        Set the QI strategy to use.
        
        Args:
            strategy: QI strategy ('mbqi', 'ematching', 'combined', or 'auto')
        Raises:
            ValueError: If strategy is not supported
        """
        valid_strategies = ['mbqi', 'ematching', 'combined', 'auto']
        if strategy not in valid_strategies:
            raise ValueError(f"Unsupported QI strategy: {strategy}. Supported: {valid_strategies}")
        self.qi_strategy = strategy
        if self.verbose:
            logger.info("Set QI strategy to: %s", strategy)
