"""
Solving Exists-Forall problems over floating-point variables using CEGIS.
"""
from typing import List, Optional, Dict
import logging
import z3

logger = logging.getLogger(__name__)


def cegis_efsmt_fp(x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, 
                   max_loops: Optional[int] = None, timeout: Optional[int] = None) -> str:
    """Solve EFSMT problems over floating-point variables using CEGIS algorithm."""
    max_loops = max_loops or 100
    candidate = {var: z3.FPVal(0.0, var.sort()) for var in x}
    
    for loop in range(max_loops):
        logger.debug(f"CEGIS iteration {loop + 1}")
        
        # Synthesize candidate
        result = _synthesize_candidate(x, y, phi, candidate, timeout)
        if result == "unsat":
            return "unsat"
        elif result == "unknown":
            return "unknown"
        
        # Verify candidate
        result = _verify_candidate(x, y, phi, candidate, timeout)
        if result == "unsat":  # No counterexample found
            return "sat"
        elif result == "unknown":
            return "unknown"
        
        # Refine with counterexample
        counterexample = _extract_counterexample(x, y, phi, candidate)
        if counterexample is None:
            return "unknown"
        
        # Simple perturbation to avoid current counterexample
        for var in x:
            current_val = candidate[var]
            perturbation = z3.FPVal(0.1, var.sort())
            candidate[var] = z3.fpAdd(z3.RNE(), current_val, perturbation)
    
    logger.warning(f"CEGIS reached maximum iterations ({max_loops})")
    return "unknown"


def _synthesize_candidate(x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, 
                         candidate: Dict, timeout: Optional[int] = None) -> str:
    """Synthesize a candidate solution for existential variables."""
    solver = z3.Solver()
    if timeout:
        solver.set("timeout", timeout * 1000)
    
    constraints = [var == value for var, value in candidate.items()]
    synthesis_formula = z3.Exists(tuple(x), 
                                 z3.And(constraints + [z3.ForAll(tuple(y), phi)]))
    solver.add(synthesis_formula)
    
    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        for var in x:
            if var in model:
                candidate[var] = model[var]
        return "sat"
    return "unsat" if result == z3.unsat else "unknown"


def _verify_candidate(x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, 
                     candidate: Dict, timeout: Optional[int] = None) -> str:
    """Verify if the candidate solution is valid for all universal variables."""
    solver = z3.Solver()
    if timeout:
        solver.set("timeout", timeout * 1000)
    
    phi_substituted = z3.substitute(phi, [(var, value) for var, value in candidate.items()])
    verification_formula = z3.Exists(tuple(y), z3.Not(phi_substituted))
    solver.add(verification_formula)
    
    result = solver.check()
    return "sat" if result == z3.sat else ("unsat" if result == z3.unsat else "unknown")


def _extract_counterexample(x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, 
                           candidate: Dict) -> Optional[Dict]:
    """Extract a counterexample from the verification phase."""
    solver = z3.Solver()
    phi_substituted = z3.substitute(phi, [(var, value) for var, value in candidate.items()])
    verification_formula = z3.Exists(tuple(y), z3.Not(phi_substituted))
    solver.add(verification_formula)
    
    if solver.check() == z3.sat:
        model = solver.model()
        return {var: model[var] for var in y if var in model}
    return None


def simple_cegis_efsmt_fp(logic: str, x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, 
                          maxloops=None, profiling=False, timeout=None) -> str:
    """Solve EFSMT over floating-point using the CEGIS algorithm."""
    logger.info(f"Solving EFSMT over floating-point with logic: {logic}")
    
    return cegis_efsmt_fp(x, y, phi, max_loops=maxloops, timeout=timeout)


def test_simple_fp_problem():
    """Test a simple floating-point EFSMT problem."""
    fp_sort = z3.FPSort(8, 24)
    x, y = z3.FP('x', fp_sort), z3.FP('y', fp_sort)
    phi = z3.fpGEQ(z3.fpAdd(z3.RNE(), x, y), z3.FPVal(0.0, fp_sort))

    # CEGIS approach
    cegis_result = simple_cegis_efsmt_fp("QF_FP", [x], [y], phi, maxloops=10)
    
    # Direct Z3 approach
    solver = z3.Solver()
    solver.add(z3.ForAll([y], phi))
    direct_result = solver.check()
    direct_result_str = "sat" if direct_result == z3.sat else ("unsat" if direct_result == z3.unsat else "unknown")
    
    print(f"CEGIS: {cegis_result}, Direct Z3: {direct_result_str}, Match: {cegis_result == direct_result_str}")
    return cegis_result, direct_result_str


if __name__ == "__main__":
    test_simple_fp_problem()