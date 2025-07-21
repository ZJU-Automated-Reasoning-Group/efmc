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
from typing import Optional, List

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
        self.invariant = None

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
        
        # Declare inv function
        inv = self._create_inv_function()
        inv_decl = f"(declare-fun inv ("
        inv_decl += " ".join(arg.sexpr() for arg in inv.domain())
        inv_decl += f") {inv.range().sexpr()})\n"
        smt2_content += inv_decl
        
        # Add verification conditions
        for vc in verification_conditions:
            smt2_content += f"(assert {vc.sexpr()})\n"
        
        smt2_content += "(check-sat)\n"
        if logic != "UFBV":  # Some solvers don't support get-model for UFBV
            smt2_content += "(get-model)\n"
        
        return smt2_content

    def _call_external_solver(self, smt2_content: str) -> str:
        """Call external solver with SMT-LIB2 content."""
        solver_configs = {
            'z3': [config.z3_exec],
            'cvc5': [config.cvc5_exec, '-q', '--produce-models'],
            'yices': [config.yices_exec],
            'mathsat': [config.math_exec],
            'bitwuzla': [config.bitwuzla_exec],
            'boolector': [config.btor_exec]
        }
        
        if self.solver_name not in solver_configs:
            raise ValueError(f"Unsupported external solver: {self.solver_name}")
        
        if not config.check_available(self.solver_name):
            raise FileNotFoundError(f"Solver {self.solver_name} not found")

        # Create temporary file
        tmp_file = f"/tmp/qi_prover_{uuid.uuid1()}.smt2"
        try:
            with open(tmp_file, 'w') as f:
                f.write(smt2_content)
            
            # Run solver
            cmd = solver_configs[self.solver_name] + [tmp_file]
            process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            
            if self.timeout:
                try:
                    stdout, stderr = process.communicate(timeout=self.timeout)
                except subprocess.TimeoutExpired:
                    process.kill()
                    return "timeout"
            else:
                stdout, stderr = process.communicate()
            
            output = stdout.decode('utf-8').strip()
            if stderr:
                logger.warning(f"Solver stderr: {stderr.decode('utf-8')}")
            
            return output
            
        finally:
            if os.path.exists(tmp_file):
                os.remove(tmp_file)

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """Verify using QI with specified solver."""
        if timeout is not None:
            self.timeout = timeout

        try:
            inv = self._create_inv_function()
            verification_conditions = self._build_verification_conditions(inv)
            
            if self.verbose:
                logger.info(f"QI starting with strategy: {self.qi_strategy}, solver: {self.solver_name}")

            start_time = time.time()

            if self.solver_name == 'z3api':
                # Use Z3 Python API
                solver = self._configure_z3_solver()
                for vc in verification_conditions:
                    solver.add(vc)
                
                result = solver.check()
                
                if result == z3.sat:
                    model = solver.model()
                    self.invariant = model.eval(inv(*self.sts.variables))
                    if self.verbose:
                        logger.info(f"QI succeeded in {time.time() - start_time:.2f}s")
                    return VerificationResult(True, self.invariant)
                elif result == z3.unsat:
                    return VerificationResult(False, None, None, is_unknown=True)
                else:
                    return VerificationResult(False, None, None, is_unknown=True)
            
            else:
                # Use external solver via SMT-LIB2
                smt2_content = self._generate_smtlib2(verification_conditions)
                
                # Dump to file if requested
                if self.dump_file:
                    with open(self.dump_file, 'w') as f:
                        f.write(smt2_content)
                    logger.info(f"SMT-LIB2 dumped to {self.dump_file}")
                    return VerificationResult(False, None, None, is_unknown=True)  # Just dump, don't solve
                
                # Call external solver
                output = self._call_external_solver(smt2_content)
                
                if "timeout" in output:
                    return VerificationResult(False, None, None, is_timeout=True, is_unknown=True)
                elif "unsat" in output:
                    return VerificationResult(False, None, None, is_unknown=True)
                elif "sat" in output:
                    if self.verbose:
                        logger.info(f"External QI succeeded in {time.time() - start_time:.2f}s")
                    # For external solvers, we can't easily extract the invariant
                    return VerificationResult(True, None)
                else:
                    return VerificationResult(False, None, None, is_unknown=True)

        except Exception as e:
            logger.error(f"QI solving error: {e}")
            return VerificationResult(False, None, None, is_unknown=True)

    def try_multiple_strategies(self) -> VerificationResult:
        """Try multiple QI strategies."""
        strategies = ['mbqi', 'ematching', 'combined']
        
        for strategy in strategies:
            if self.verbose:
                logger.info(f"Trying QI strategy: {strategy}")
            self.qi_strategy = strategy
            result = self.solve()
            if result.is_safe:
                return result
        
        return VerificationResult(False, None, None, is_unknown=True)

    def set_strategy(self, strategy: str) -> None:
        """Set QI strategy."""
        valid_strategies = ['mbqi', 'ematching', 'combined', 'auto']
        if strategy not in valid_strategies:
            raise ValueError(f"Invalid strategy: {strategy}")
        self.qi_strategy = strategy

    def get_invariant(self) -> Optional[z3.ExprRef]:
        """Get found invariant."""
        return self.invariant
