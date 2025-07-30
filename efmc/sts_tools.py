"""
Transition System Tools

This module provides utility functions for working with transition systems,
including simulation capabilities.
"""

from typing import List, Dict, Any, Optional
import z3
from .sts import TransitionSystem


def simulate_transition_system(ts: TransitionSystem, steps: int = 10, 
                             random_seed: Optional[int] = None, 
                             concrete_init: Optional[Dict[str, Any]] = None) -> List[Dict[str, Any]]:
    """Simulate transition system execution.
    
    Args:
        ts: The transition system to simulate
        steps: Number of simulation steps
        random_seed: Optional seed for random choices
        concrete_init: Optional initial state dictionary {var_name: value}
        
    Returns:
        List of states as dictionaries mapping variable names to values
    """
    assert ts.initialized
    
    if random_seed is not None:
        import random
        random.seed(random_seed)

    solver = z3.Solver()
    
    # Initialize state
    state = _get_initial_state(ts, solver, concrete_init)
    trace = [state.copy()]

    # Simulate steps
    for _ in range(steps):
        next_state = _get_next_state(ts, solver, state)
        if next_state is None:
            break  # No valid next state
            
        state = next_state
        trace.append(state.copy())
        
        # Check post-condition violation
        if _check_post_violation(ts, solver, state):
            print(f"Post-condition violated at step {len(trace) - 1}")

    return trace


def _get_initial_state(ts: TransitionSystem, solver: z3.Solver, 
                      concrete_init: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    """Get initial state, either from concrete_init or by solving init condition."""
    if concrete_init:
        # Verify provided initial state
        state_constraints = [var == concrete_init[str(var)] 
                           for var in ts.variables if str(var) in concrete_init]
        solver.push()
        solver.add(z3.And(state_constraints + [ts.init]))
        if solver.check() != z3.sat:
            solver.pop()
            raise ValueError("Provided initial state does not satisfy init condition")
        solver.pop()
        return concrete_init.copy()
    else:
        # Generate initial state from init condition
        solver.push()
        solver.add(ts.init)
        if solver.check() != z3.sat:
            solver.pop()
            raise ValueError("Init condition is unsatisfiable")
        
        model = solver.model()
        state = {str(var): model.eval(var, model_completion=True) for var in ts.variables}
        solver.pop()
        return state


def _get_next_state(ts: TransitionSystem, solver: z3.Solver, 
                   current_state: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Get next state from current state using transition relation."""
    state_constraints = [var == current_state[str(var)] 
                        for var in ts.variables if str(var) in current_state]
    
    solver.push()
    solver.add(z3.And(state_constraints + [ts.trans]))
    
    if solver.check() != z3.sat:
        solver.pop()
        return None
        
    model = solver.model()
    next_state = {}
    
    # Map prime variables back to regular variables
    for var in ts.variables:
        var_name = str(var)
        for prime_var in ts.prime_variables:
            prime_name = str(prime_var)
            if (prime_name.endswith("!") and prime_name[:-1] == var_name) or \
               (prime_name.endswith("'") and prime_name[:-1] == var_name) or \
               (prime_name.endswith("_p") and prime_name[:-2] == var_name):
                next_state[var_name] = model.eval(prime_var, model_completion=True)
                break
    
    solver.pop()
    return next_state


def _check_post_violation(ts: TransitionSystem, solver: z3.Solver, 
                         state: Dict[str, Any]) -> bool:
    """Check if post-condition is violated in given state."""
    state_constraints = [var == state[str(var)] 
                        for var in ts.variables if str(var) in state]
    
    solver.push()
    solver.add(z3.And(state_constraints + [z3.Not(ts.post)]))
    result = solver.check() == z3.sat
    solver.pop()
    return result 