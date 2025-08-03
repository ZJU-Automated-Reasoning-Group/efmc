"""
Quantifier Instantiation (QI) based verification using SMT solvers with quantifier support.
Supports Z3 API, SMT-LIB2 dumping, and external solvers like CVC5.
"""

import logging
import time
import tempfile
import subprocess
import os
import uuid
from typing import Optional, List, Dict, Any

import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult
from efmc.efmc_config import config

logger = logging.getLogger(__name__)


class QuantifierInstantiationProver:
    def __init__(self, system: TransitionSystem, **kwargs):
        self.sts = system
        self.timeout = kwargs.get('timeout', None)
        self.qi_strategy = kwargs.get('qi_strategy', 'auto')
        self.solver_name = kwargs.get('solver', 'z3api')
        self.verbose = kwargs.get('verbose', False)
        self.dump_file = kwargs.get('dump_file', None)
        self.invariant: Optional[z3.ExprRef] = None

    def _get_logic(self) -> str:
        """Get appropriate SMT logic based on variable types."""
        if self.sts.has_int:
            return "UFLIA"
        elif self.sts.has_real:
            return "AUFLIRA"
        elif self.sts.has_bv:
            return "UFBV"
        else:
            raise NotImplementedError("Unsupported variable types")

    def _create_inv_function(self) -> z3.FuncDeclRef:
        """Create invariant function with appropriate signature."""
        if self.sts.has_int:
            arg_sorts = [z3.IntSort() for _ in self.sts.variables]
        elif self.sts.has_real:
            arg_sorts = [z3.RealSort() for _ in self.sts.variables]
        elif self.sts.has_bv:
            bv_size = self.sts.variables[0].sort().size()
            arg_sorts = [z3.BitVecSort(bv_size) for _ in self.sts.variables]
        else:
            raise NotImplementedError("Unsupported variable types")

        return z3.Function('inv', *(arg_sorts + [z3.BoolSort()]))

    def _configure_z3_solver(self) -> z3.Solver:
        """Configure Z3 solver with QI strategy."""
        s = z3.SolverFor(self._get_logic())
        
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

        if self.timeout:
            s.set('timeout', self.timeout * 1000)

        return s

    def _build_verification_conditions(self, inv: z3.FuncDeclRef) -> List[z3.ExprRef]:
        """Build verification conditions: initiation, consecution, and safety."""
        return [
            # Initiation: init(X) => inv(X)
            z3.ForAll(self.sts.variables, z3.Implies(self.sts.init, inv(*self.sts.variables))),
            # Consecution: inv(X) ∧ trans(X,X') => inv(X')
            z3.ForAll(self.sts.all_variables, 
                     z3.Implies(z3.And(inv(*self.sts.variables), self.sts.trans),
                               inv(*self.sts.prime_variables))),
            # Safety: inv(X) => post(X)
            z3.ForAll(self.sts.variables, z3.Implies(inv(*self.sts.variables), self.sts.post))
        ]

    def _generate_smtlib2(self, verification_conditions: List[z3.ExprRef]) -> str:
        """Generate SMT-LIB2 format string."""
        logic = self._get_logic()
        smt2_content = f"(set-logic {logic})\n"
        
        # Declare variables
        for var in self.sts.all_variables:
            smt2_content += f"(declare-const {var.sexpr()} {var.sort().sexpr()})\n"
        
        # Add verification conditions
        for i, vc in enumerate(verification_conditions):
            smt2_content += f"(assert {vc.sexpr()})\n"
        
        smt2_content += "(check-sat)\n"
        return smt2_content

    def _call_external_solver(self, smt2_content: str) -> str:
        """Call external SMT solver (CVC5, Z3, etc.)"""
        if self.solver_name == 'cvc5':
            solver_cmd = ['cvc5', '--lang=smt2']
        elif self.solver_name == 'z3':
            solver_cmd = ['z3', '-smt2']
        else:
            raise ValueError(f"Unsupported external solver: {self.solver_name}")
        
        # Write SMT2 content to temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
            f.write(smt2_content)
            temp_file = f.name
        
        try:
            # Call external solver
            result = subprocess.run(
                solver_cmd + [temp_file],
                capture_output=True,
                text=True,
                timeout=self.timeout if self.timeout else 60
            )
            
            if result.returncode == 0:
                return result.stdout.strip()
            else:
                logger.warning(f"External solver failed: {result.stderr}")
                return "unknown"
                
        except subprocess.TimeoutExpired:
            logger.warning("External solver timed out")
            return "unknown"
        except Exception as e:
            logger.error(f"Error calling external solver: {e}")
            return "unknown"
        finally:
            # Clean up temporary file
            try:
                os.unlink(temp_file)
            except:
                pass

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """Solve verification problem using quantifier instantiation."""
        if timeout:
            self.timeout = timeout
            
        logger.info(f"Starting QI verification with strategy: {self.qi_strategy}")
        start_time = time.time()
        
        try:
            # Create invariant function
            inv = self._create_inv_function()
            
            # Build verification conditions
            vcs = self._build_verification_conditions(inv)
            
            if self.solver_name == 'z3api':
                # Use Z3 API
                s = self._configure_z3_solver()
                for vc in vcs:
                    s.add(vc)
                
                result = s.check()
                elapsed_time = time.time() - start_time
                
                if result == z3.sat:
                    logger.info("Property violation found (unsafe)")
                    return VerificationResult(False, None, is_unsafe=True)
                elif result == z3.unsat:
                    logger.info("Property proven safe")
                    # Extract invariant from the model
                    model = s.model()
                    if model:
                        self.invariant = model.eval(inv(*self.sts.variables))
                    return VerificationResult(True, self.invariant)
                else:
                    logger.info("Solver returned unknown")
                    return VerificationResult(False, None, is_unknown=True)
                    
            else:
                # Use external solver
                smt2_content = self._generate_smtlib2(vcs)
                
                if self.dump_file:
                    with open(self.dump_file, 'w') as f:
                        f.write(smt2_content)
                
                result = self._call_external_solver(smt2_content)
                elapsed_time = time.time() - start_time
                
                if result == "sat":
                    logger.info("Property violation found (unsafe)")
                    return VerificationResult(False, None, is_unsafe=True)
                elif result == "unsat":
                    logger.info("Property proven safe")
                    return VerificationResult(True, None)  # External solver doesn't provide model
                else:
                    logger.info("Solver returned unknown")
                    return VerificationResult(False, None, is_unknown=True)
                    
        except Exception as e:
            logger.error(f"QI verification failed: {e}")
            return VerificationResult(False, None, is_unknown=True)

    def try_multiple_strategies(self) -> VerificationResult:
        """Try multiple QI strategies if current one fails."""
        strategies = ['mbqi', 'ematching', 'combined']
        
        for strategy in strategies:
            if strategy == self.qi_strategy:
                continue
                
            logger.info(f"Trying QI strategy: {strategy}")
            self.qi_strategy = strategy
            
            result = self.solve()
            if result.is_safe or result.is_unsafe:
                return result
        
        return VerificationResult(False, None, is_unknown=True)

    def set_strategy(self, strategy: str) -> None:
        """Set QI strategy."""
        valid_strategies = ['auto', 'mbqi', 'ematching', 'combined']
        if strategy not in valid_strategies:
            raise ValueError(f"Invalid strategy: {strategy}. Valid strategies: {valid_strategies}")
        self.qi_strategy = strategy

    def get_invariant(self) -> Optional[z3.ExprRef]:
        """Get the computed invariant if available."""
        return self.invariant
