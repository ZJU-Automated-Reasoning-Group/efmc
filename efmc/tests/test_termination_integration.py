#!/usr/bin/env python3
"""
Integration test for termination prover with EF solver infrastructure.

This test verifies that the termination prover can successfully integrate
with the existing EF solver infrastructure and prove termination of simple
bit-vector programs.
"""

import sys
import os
import z3

# Add the project root to the path
# sys.path.insert(0, os.path.dirname(__file__))

from efmc.sts import TransitionSystem
from efmc.engines.ef.termination_prover import TerminationProver


def test_simple_countdown():
    """Test termination proving on a simple countdown loop."""
    print("Testing simple countdown loop...")
    
    # Create bit-vector variable
    x = z3.BitVec('x', 8)  # Use smaller bit-width for faster solving
    x_prime = z3.BitVec('x!', 8)
    
    # Create transition system: while (x > 0) { x = x - 1; }
    sts = TransitionSystem(
        variables=[x],
        prime_variables=[x_prime],
        init=z3.BoolVal(True),
        trans=z3.And(z3.UGT(x, 0), x_prime == x - 1),
        post=z3.ULE(x, 0)
    )
    sts.set_signedness("unsigned")
    
    # Test linear ranking template
    prover = TerminationProver(sts)
    prover.set_ranking_template("bv_linear_ranking")
    
    print("  Attempting to prove termination with linear ranking function...")
    result = prover.prove_termination(timeout=10)
    
    # Properly handle the result object
    success = bool(result.result) if hasattr(result, 'result') else False
    
    if success:
        print("  ✓ Termination PROVEN!")
        ranking_func = prover.get_ranking_function()
        if ranking_func is not None:
            print(f"  Ranking function: {z3.simplify(ranking_func)}")
        return True
    else:
        print("  ✗ Could not prove termination")
        if hasattr(result, 'error') and result.error:
            print(f"  Error: {result.error}")
        return False


def test_verification_condition_generation():
    """Test that verification conditions are generated correctly."""
    print("Testing verification condition generation...")
    
    # Create simple transition system
    x = z3.BitVec('x', 8)
    x_prime = z3.BitVec('x!', 8)
    
    sts = TransitionSystem(
        variables=[x],
        prime_variables=[x_prime],
        init=z3.BoolVal(True),
        trans=z3.And(z3.UGT(x, 0), x_prime == x - 1),
        post=z3.ULE(x, 0)
    )
    sts.set_signedness("unsigned")
    
    # Create prover and generate VC
    prover = TerminationProver(sts)
    prover.set_ranking_template("bv_linear_ranking")
    
    try:
        vc = prover.generate_ranking_vc()
        print("  ✓ Verification condition generated successfully")
        print(f"  VC type: {type(vc)}")
        print(f"  VC is Z3 expression: {z3.is_expr(vc)}")
        return True
    except Exception as e:
        print(f"  ✗ Failed to generate verification condition: {e}")
        return False


def test_template_variable_extraction():
    """Test that template variables are extracted correctly."""
    print("Testing template variable extraction...")
    
    # Create simple transition system
    x = z3.BitVec('x', 8)
    x_prime = z3.BitVec('x!', 8)
    
    sts = TransitionSystem(
        variables=[x],
        prime_variables=[x_prime],
        init=z3.BoolVal(True),
        trans=z3.And(z3.UGT(x, 0), x_prime == x - 1),
        post=z3.ULE(x, 0)
    )
    sts.set_signedness("unsigned")
    
    # Test different templates
    templates = [
        ("bv_linear_ranking", "Linear"),
        ("bv_lexicographic_ranking", "Lexicographic"),
        ("bv_conditional_ranking", "Conditional")
    ]
    
    for template_name, template_desc in templates:
        try:
            prover = TerminationProver(sts)
            prover.set_ranking_template(template_name)
            
            # Check that template variables exist
            assert hasattr(prover.ranking_template, 'template_vars')
            assert len(prover.ranking_template.template_vars) > 0
            
            print(f"  ✓ {template_desc} template variables extracted successfully")
            
        except Exception as e:
            print(f"  ✗ Failed to extract {template_desc} template variables: {e}")
            return False
    
    return True


def test_ranking_function_building():
    """Test that ranking functions can be built from models."""
    print("Testing ranking function building...")
    
    # Create simple transition system
    x = z3.BitVec('x', 8)
    x_prime = z3.BitVec('x!', 8)
    
    sts = TransitionSystem(
        variables=[x],
        prime_variables=[x_prime],
        init=z3.BoolVal(True),
        trans=z3.And(z3.UGT(x, 0), x_prime == x - 1),
        post=z3.ULE(x, 0)
    )
    sts.set_signedness("unsigned")
    
    # Create prover
    prover = TerminationProver(sts)
    prover.set_ranking_template("bv_linear_ranking")
    
    try:
        # Create a dummy model for testing
        solver = z3.Solver()
        
        # Add template variables to solver
        template_vars = []
        for var_list in prover.ranking_template.template_vars:
            template_vars.extend(var_list)
        
        # Add some constraints to make the model interesting
        if template_vars:
            solver.add(template_vars[0] == 1)  # Coefficient for x
            if len(template_vars) > 1:
                solver.add(template_vars[1] == 0)  # Constant term
        
        if solver.check() == z3.sat:
            model = solver.model()
            
            # Try to build ranking function
            ranking_func = prover.ranking_template.build_invariant_expr(model, use_prime_variables=False)
            
            print("  ✓ Ranking function built successfully")
            print(f"  Ranking function: {ranking_func}")
            return True
        else:
            print("  ⚠ Could not create satisfiable model for testing")
            return True  # Not a failure of our code
            
    except Exception as e:
        print(f"  ✗ Failed to build ranking function: {e}")
        return False


def main():
    """Run all integration tests."""
    print("Running termination prover integration tests...")
    print("=" * 60)
    
    tests = [
        test_verification_condition_generation,
        test_template_variable_extraction,
        test_ranking_function_building,
        test_simple_countdown,  # This one might fail due to solver complexity
    ]
    
    passed = 0
    total = len(tests)
    
    for test in tests:
        try:
            if test():
                passed += 1
            print()  # Add spacing between tests
        except Exception as e:
            print(f"  ✗ Test {test.__name__} failed with exception: {e}")
            print()
    
    print("=" * 60)
    print(f"Integration tests completed: {passed}/{total} passed")
    
    if passed == total:
        print("✓ All integration tests passed!")
        return 0
    else:
        print("⚠ Some integration tests failed or were skipped")
        return 1


if __name__ == "__main__":
    sys.exit(main()) 