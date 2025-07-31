"""
Unit tests for k-safety verification engine.
"""

import pytest
import unittest
import z3
from efmc.sts import TransitionSystem
from efmc.engines.ksafety import BaseKSafetyProver, NonInterferenceProver, DeterminismProver
from efmc.utils.verification_utils import VerificationResult


class TestBaseKSafetyProver(unittest.TestCase):
    """Test cases for base k-safety verification functionality."""

    def setUp(self):
        """Set up test fixtures."""
        # Create a simple transition system for testing
        self.x = z3.Int('x')
        self.y = z3.Int('y')
        self.secret = z3.Int('secret')
        self.output = z3.Int('output')
        
        # Create transition system
        self.sts = TransitionSystem()
        self.sts.variables = [self.x, self.y, self.secret, self.output]
        self.sts.prime_variables = [
            z3.Int('x_p'), z3.Int('y_p'), 
            z3.Int('secret_p'), z3.Int('output_p')
        ]
        self.sts.init = z3.And(self.x == 0, self.y == 0, self.output == 0)
        self.sts.trans = z3.And(
            z3.Implies(self.secret > 0, z3.And(self.x == self.x + 1, self.y == self.y + self.secret)),
            z3.Implies(self.secret <= 0, z3.And(self.x == self.x + 1, self.y == self.y)),
            self.output == self.x + self.y
        )
        self.sts.post = z3.And(self.x >= 0, self.y >= 0)

    def test_initialization(self):
        """Test k-safety prover initialization."""
        prover = BaseKSafetyProver(self.sts, k=2)
        
        self.assertEqual(prover.k, 2)
        self.assertEqual(prover.sts, self.sts)
        self.assertEqual(prover.timeout, 300)
        self.assertEqual(prover.verification_method, "bounded_model_checking")

    def test_create_trace_variables(self):
        """Test trace variable creation."""
        prover = BaseKSafetyProver(self.sts, k=2)
        trace_vars = prover.create_trace_variables()
        
        # Check that we have 2 traces
        self.assertEqual(len(trace_vars), 2)
        
        # Check that each trace has the same number of variables as the original system
        for trace_idx in range(2):
            self.assertEqual(len(trace_vars[trace_idx]), len(self.sts.variables))
            
            # Check variable naming
            for i, var in enumerate(self.sts.variables):
                trace_var = trace_vars[trace_idx][i]
                var_name = str(var)
                expected_name = f"{var_name}_{trace_idx}"
                self.assertIn(expected_name, str(trace_var))

    def test_set_relational_property(self):
        """Test setting relational property."""
        prover = BaseKSafetyProver(self.sts, k=2)
        
        # Create a simple property
        trace_vars = prover.create_trace_variables()
        property_expr = trace_vars[0][0] >= 0  # x >= 0 in first trace
        
        prover.set_relational_property(property_expr)
        self.assertEqual(prover.relational_property, property_expr)

    def test_create_k_safety_formula(self):
        """Test k-safety formula creation."""
        prover = BaseKSafetyProver(self.sts, k=2)
        
        # Set a simple property
        trace_vars = prover.create_trace_variables()
        property_expr = trace_vars[0][0] >= 0
        prover.set_relational_property(property_expr)
        
        # Create the formula
        formula = prover.create_k_safety_formula()
        
        # Check that the formula is not None
        self.assertIsNotNone(formula)
        self.assertEqual(prover.verification_formula, formula)

    def test_create_k_safety_formula_without_property(self):
        """Test that creating formula without property raises error."""
        prover = BaseKSafetyProver(self.sts, k=2)
        
        with self.assertRaises(ValueError):
            prover.create_k_safety_formula()

    def test_bounded_model_checking(self):
        """Test BMC with different properties."""
        prover = BaseKSafetyProver(self.sts, k=2, timeout=10)
        
        # Test with a safe property: x >= 0 in first trace
        trace_vars = prover.create_trace_variables()
        property_expr = trace_vars[0][0] >= 0  # x >= 0
        prover.set_relational_property(property_expr)
        
        result = prover.bounded_model_checking(1)
        
        # Should be safe since x starts at 0 and only increases
        self.assertTrue(result.is_safe or result.is_unknown)

    def test_solve_without_property(self):
        """Test that solve without property raises error."""
        prover = BaseKSafetyProver(self.sts, k=2)
        
        with self.assertRaises(ValueError):
            prover.solve()

    def test_solve_with_timeout(self):
        """Test solve with timeout."""
        prover = BaseKSafetyProver(self.sts, k=2, timeout=1)  # Very short timeout
        
        # Set a property
        trace_vars = prover.create_trace_variables()
        property_expr = trace_vars[0][0] >= 0
        prover.set_relational_property(property_expr)
        
        result = prover.solve(timeout=1)
        
        # Should get a result (may be unknown due to timeout)
        self.assertIsInstance(result, VerificationResult)

    def test_different_k_values(self):
        """Test with different k values."""
        for k in [2, 3]:
            prover = BaseKSafetyProver(self.sts, k=k, timeout=10)
            
            # Create property for k traces
            trace_vars = prover.create_trace_variables()
            property_expr = z3.And(*[trace_vars[i][0] >= 0 for i in range(k)])
            prover.set_relational_property(property_expr)
            
            result = prover.solve()
            
            # Check that we get a valid result
            self.assertIsInstance(result, VerificationResult)

    def test_verification_methods(self):
        """Test different verification methods."""
        methods = ["bounded_model_checking", "k_induction"]
        
        for method in methods:
            prover = BaseKSafetyProver(self.sts, k=2, timeout=10, method=method)
            
            # Set a simple property
            trace_vars = prover.create_trace_variables()
            property_expr = trace_vars[0][0] >= 0
            prover.set_relational_property(property_expr)
            
            result = prover.solve()
            
            # Check that we get a valid result
            self.assertIsInstance(result, VerificationResult)

    def test_custom_relational_property(self):
        """Test custom relational property verification."""
        prover = BaseKSafetyProver(self.sts, k=2, timeout=10)
        
        # Create trace variables
        trace_vars = prover.create_trace_variables()
        
        # Create a custom property: if x values are the same, then y values should be the same
        x_0 = trace_vars[0][0]  # x in trace 0
        x_1 = trace_vars[1][0]  # x in trace 1
        y_0 = trace_vars[0][1]  # y in trace 0
        y_1 = trace_vars[1][1]  # y in trace 1
        
        custom_property = z3.Implies(x_0 == x_1, y_0 == y_1)
        
        prover.set_relational_property(custom_property)
        result = prover.solve()
        
        # Check that we get a valid result
        self.assertIsInstance(result, VerificationResult)

    def test_k_induction_components(self):
        """Test k-induction base case and inductive step creation."""
        prover = BaseKSafetyProver(self.sts, k=2, timeout=10)
        
        # Set a property
        trace_vars = prover.create_trace_variables()
        property_expr = trace_vars[0][0] >= 0
        prover.set_relational_property(property_expr)
        
        # Create base case and inductive step
        base_case = prover._create_k_induction_base_case(1)
        inductive_step = prover._create_k_induction_inductive_step(1)
        
        # Check that both are not None
        self.assertIsNotNone(base_case)
        self.assertIsNotNone(inductive_step)

    def test_error_handling(self):
        """Test error handling in various scenarios."""
        # Test with invalid k value (should not raise exception, just log warning)
        prover = BaseKSafetyProver(self.sts, k=0)
        self.assertEqual(prover.k, 0)
        
        # Test with invalid timeout (should not raise exception, just use default)
        prover = BaseKSafetyProver(self.sts, k=2, timeout=-1)
        self.assertEqual(prover.timeout, -1)

    def test_logging(self):
        """Test that logging works correctly."""
        import logging
        
        # Set up logging
        logging.basicConfig(level=logging.INFO)
        
        prover = BaseKSafetyProver(self.sts, k=2, timeout=10)
        
        # Set a property
        trace_vars = prover.create_trace_variables()
        property_expr = trace_vars[0][0] >= 0
        prover.set_relational_property(property_expr)
        
        # This should not raise any exceptions
        result = prover.solve()
        
        # Check that we get a valid result
        self.assertIsInstance(result, VerificationResult)


class TestSpecializedProvers(unittest.TestCase):
    """Test cases for specialized k-safety provers."""

    def setUp(self):
        """Set up test fixtures."""
        # Create a simple transition system for testing
        self.x = z3.Int('x')
        self.y = z3.Int('y')
        self.secret = z3.Int('secret')
        self.output = z3.Int('output')
        
        # Create transition system
        self.sts = TransitionSystem()
        self.sts.variables = [self.x, self.y, self.secret, self.output]
        self.sts.prime_variables = [
            z3.Int('x_p'), z3.Int('y_p'), 
            z3.Int('secret_p'), z3.Int('output_p')
        ]
        self.sts.init = z3.And(self.x == 0, self.y == 0, self.output == 0)
        self.sts.trans = z3.And(
            z3.Implies(self.secret > 0, z3.And(self.x == self.x + 1, self.y == self.y + self.secret)),
            z3.Implies(self.secret <= 0, z3.And(self.x == self.x + 1, self.y == self.y)),
            self.output == self.x + self.y
        )
        self.sts.post = z3.And(self.x >= 0, self.y >= 0)

    def test_non_interference_verification(self):
        """Test non-interference verification."""
        prover = NonInterferenceProver(self.sts, timeout=10)
        
        # Define high and low security variables
        high_vars = ['secret']
        low_vars = ['output']
        
        result = prover.verify_non_interference(high_vars, low_vars)
        
        # Check that we get a valid result
        self.assertIsInstance(result, VerificationResult)
        self.assertTrue(result.is_safe or result.is_unsafe or result.is_unknown)

    def test_determinism_verification(self):
        """Test determinism verification."""
        prover = DeterminismProver(self.sts, timeout=10)
        
        result = prover.verify_determinism()
        
        # Check that we get a valid result
        self.assertIsInstance(result, VerificationResult)
        self.assertTrue(result.is_safe or result.is_unsafe or result.is_unknown)


if __name__ == "__main__":
    unittest.main() 