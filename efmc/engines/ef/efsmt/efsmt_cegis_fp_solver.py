"""
Solving Exists-Forall problems over floating-point variables using CEGIS.

As pysmt does not support QF_FP, we only use z3py here.
"""
from typing import List, Optional, Dict, Tuple
import logging
import z3

logger = logging.getLogger(__name__)


def simple_cegis_efsmt_fp(logic: str, x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, 
                          maxloops=None, profiling=False, timeout=None) -> Tuple[str, Optional[z3.ModelRef]]:
    maxloops = maxloops or 100
    
    logger.info(f"Solving EFSMT over floating-point with logic: {logic}, maxloops: {maxloops}")
    
    # Create synthesis solver for existential variables
    synthesis_solver = z3.Solver()
    if timeout:
        synthesis_solver.set("timeout", timeout * 1000)
    
    # Start with no constraints (just True)
    synthesis_solver.add(z3.BoolVal(True))
    
    for loop in range(maxloops):
        logger.debug(f"CEGIS iteration {loop + 1}")
        
        # Synthesize: Find a candidate solution for existential variables
        result = synthesis_solver.check()
        if result == z3.unsat:
            logger.info("Synthesis solver returned UNSAT - no solution exists")
            return "unsat", None
        elif result == z3.unknown:
            logger.warning("Synthesis solver returned UNKNOWN")
            return "unknown", None
        
        # Extract candidate solution
        model = synthesis_solver.model()
        candidate = {}
        for var in x:
            try:
                val = model.eval(var, True)
                if val is not None:
                    candidate[var] = val
            except:
                # Use default value if model doesn't provide one
                if var.sort().name() == "FPSort":
                    candidate[var] = z3.FPVal(0.0, var.sort())
                else:
                    # For non-FP variables, use a reasonable default
                    candidate[var] = z3.IntVal(0) if var.sort().name() == "Int" else z3.RealVal(0)
        
        # Verify: Check if candidate works for all universal variables
        # Substitute candidate values into phi
        phi_substituted = z3.substitute(phi, [(var, value) for var, value in candidate.items()])
        
        # Check if Not(phi_substituted) is satisfiable (i.e., if there's a counterexample)
        verification_solver = z3.Solver()
        if timeout:
            verification_solver.set("timeout", timeout * 1000)
        
        verification_solver.add(z3.Not(phi_substituted))
        
        result = verification_solver.check()
        if result == z3.unsat:
            # No counterexample found - candidate is valid
            logger.info(f"Found valid solution after {loop + 1} iterations")
            # print("model: ", model)
            return "sat", model
        elif result == z3.unknown:
            logger.warning("Verification solver returned UNKNOWN")
            return "unknown", None
        
        # Extract counterexample and add as constraint
        counterexample_model = verification_solver.model()
        counterexample = {}
        for var in y:
            try:
                val = counterexample_model.eval(var, True)
                if val is not None:
                    counterexample[var] = val
            except:
                pass
        
        # Add counterexample as constraint to synthesis solver
        phi_with_counterexample = z3.substitute(phi, [(var, value) for var, value in counterexample.items()])
        synthesis_solver.add(phi_with_counterexample)
        
        logger.debug(f"Added counterexample constraint, synthesis solver now has {synthesis_solver.num_scopes()} constraints")
    
    logger.warning(f"CEGIS reached maximum iterations ({maxloops})")
    return "unknown", None


# Keep the old function name for backward compatibility
def cegis_efsmt_fp(x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, 
                   max_loops: Optional[int] = None, timeout: Optional[int] = None) -> Tuple[str, Optional[z3.ModelRef]]:
    """
    Legacy function - now just calls simple_cegis_efsmt_fp for backward compatibility.
    """
    return simple_cegis_efsmt_fp("QF_FP", x, y, phi, maxloops=max_loops, timeout=timeout)


def test_simple_fp_problem():
    """Test a simple floating-point EFSMT problem."""
    fp_sort = z3.FPSort(8, 24)
    x, y = z3.FP('x', fp_sort), z3.FP('y', fp_sort)
    phi = z3.fpGEQ(z3.fpAdd(z3.RNE(), x, y), z3.FPVal(0.0, fp_sort))

    # CEGIS approach
    cegis_result, cegis_model = simple_cegis_efsmt_fp("QF_FP", [x], [y], phi, maxloops=10)
    
    # Direct Z3 approach
    solver = z3.Solver()
    solver.add(z3.ForAll([y], phi))
    direct_result = solver.check()
    direct_result_str = "sat" if direct_result == z3.sat else ("unsat" if direct_result == z3.unsat else "unknown")
    
    print(f"CEGIS: {cegis_result}, Direct Z3: {direct_result_str}, Match: {cegis_result == direct_result_str}")
    if cegis_result == "sat" and cegis_model is not None:
        print(f"CEGIS model: {cegis_model}")
    return cegis_result, direct_result_str


if __name__ == "__main__":
    test_simple_fp_problem()
    