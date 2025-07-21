#!/usr/bin/env python3
"""
Test to verify that the found danger invariants are meaningful
"""

import z3


def test_nested_loop_invariant():
    """
    Test the nested loop danger invariant manually
    """
    print("=== Testing Nested Loop Danger Invariant ===")
    
    # Variables
    i, j, n = z3.Ints('i j n')
    
    # The danger invariant found was:
    # Or(51 + 0*i + 51*j + 51*n >= 0, ..., Implies(True, j >= 51), ...)
    # Simplified: j >= 51 (since the first disjunct is always true)
    danger_inv = j >= 51
    
    print(f"Danger invariant: {danger_inv}")
    
    # Test: Can this danger invariant reach error states?
    # Error condition: i*j > 50
    error_condition = i * j > 50
    
    solver = z3.Solver()
    solver.add(danger_inv)
    solver.add(error_condition)
    
    if solver.check() == z3.sat:
        model = solver.model()
        print(f"✓ Danger invariant can reach error: i={model[i]}, j={model[j]}")
        i_val = model[i].as_long() if model[i] is not None else 0
        j_val = model[j].as_long() if model[j] is not None else 51
        product = i_val * j_val
        print(f"  Product i*j = {product} > 50: {product > 50}")
    else:
        print("✗ Danger invariant cannot reach error states")
    
    # Test: Is the danger invariant inductive?
    print("\nTesting inductiveness...")
    
    # Transition relation (simplified)
    ip, jp, np = z3.Ints('ip jp np')
    trans = z3.And(
        np == n,
        z3.If(j < i,
              z3.And(jp == j + 1, ip == i),
              z3.If(i < n,
                    z3.And(ip == i + 1, jp == 0),
                    z3.And(ip == i, jp == j)
              )
        )
    )
    
    danger_inv_prime = z3.substitute(danger_inv, [(j, jp)])
    
    # Check: danger_inv ∧ trans ⇒ danger_inv'
    solver = z3.Solver()
    solver.add(danger_inv)
    solver.add(trans)
    solver.add(z3.Not(danger_inv_prime))
    
    if solver.check() == z3.unsat:
        print("✓ Danger invariant is inductive")
    else:
        print("✗ Danger invariant is not inductive")
        if solver.check() == z3.sat:
            model = solver.model()
            print(f"  Counterexample: i={model[i]}, j={model[j]}, n={model[n]}")
            print(f"  After transition: i'={model[ip]}, j'={model[jp]}")


def test_simple_counter_danger():
    """
    Test why even simple safe systems get flagged as unsafe
    """
    print("\n=== Testing Simple Counter (Should be Safe) ===")
    
    x = z3.Int('x')
    xp = z3.Int('xp')
    
    # System: x starts at 0, increments to max 49, then stops
    # This should be safe for property x < 50
    init = x == 0
    trans = z3.If(x < 49, xp == x + 1, xp == x)
    post = x < 50
    
    print(f"Initial: {init}")
    print(f"Transition: {trans}")
    print(f"Safety: {post}")
    
    # The trivial danger invariant is True
    danger_inv = z3.BoolVal(True)
    
    # Check: Can danger invariant reach error?
    solver = z3.Solver()
    solver.add(danger_inv)
    solver.add(z3.Not(post))  # Error states
    
    if solver.check() == z3.sat:
        model = solver.model()
        print(f"✓ Danger invariant True can reach error: x={model[x]}")
        print("  This is why we get false positives - True over-approximates everything!")
    
    # Check: Does initial state imply danger invariant?
    solver = z3.Solver()
    solver.add(init)
    solver.add(z3.Not(danger_inv))
    
    if solver.check() == z3.unsat:
        print("✓ Initial state implies danger invariant True")
        print("  This is why the system is flagged as unsafe")
    
    # The real question: Can we actually reach error states from initial state?
    print("\nChecking actual reachability...")
    
    # Simulate a few steps
    solver = z3.Solver()
    solver.add(init)  # x = 0
    
    # After many transitions, can we reach x >= 50?
    x1 = z3.Int('x1')
    solver.add(z3.If(x < 49, x1 == x + 1, x1 == x))  # One step
    
    x2 = z3.Int('x2') 
    solver.add(z3.If(x1 < 49, x2 == x1 + 1, x2 == x1))  # Two steps
    
    # Continue for many steps...
    current_x = x2
    for i in range(50):  # 50 more steps
        next_x = z3.Int(f'x{i+3}')
        solver.add(z3.If(current_x < 49, next_x == current_x + 1, next_x == current_x))
        current_x = next_x
    
    # Can we reach error?
    solver.add(current_x >= 50)
    
    if solver.check() == z3.sat:
        model = solver.model()
        print(f"✗ Can actually reach error: final x={model[current_x]}")
    else:
        print("✓ Cannot actually reach error states (system is truly safe)")
        print("  The danger invariant approach gives false positive due to over-approximation")


if __name__ == "__main__":
    test_nested_loop_invariant()
    test_simple_counter_danger() 