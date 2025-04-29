"""
TBD: by LLM, to check.
"""

import unittest
from unittest.mock import Mock, patch
import sys
import os
from z3 import And, Real, Not, BoolVal, is_and

from efmc.engines.ef.farkas.farkas_inv import FarkasTemplate
from efmc.engines.ef.farkas.farkas import FarkasLemma
from efmc.sts import TransitionSystem


class TestFarkasTemplate(unittest.TestCase):

    def setUp(self):
        """Set up test fixtures before each test method."""
        # Create a mock TransitionSystem
        self.mock_sts = Mock(spec=TransitionSystem)
        self.mock_sts.variables = [Real('x'), Real('y')]
        self.mock_sts.prime_variables = [Real('x_prime'), Real('y_prime')]
        self.mock_sts.init = BoolVal(True)
        self.mock_sts.trans = BoolVal(True)
        self.mock_sts.post = BoolVal(True)

        # Create a concrete subclass of FarkasTemplate to test with
        class ConcreteFarkasTemplate(FarkasTemplate):
            def build_invariant_expr(self, model, use_prime_variables=False):
                return BoolVal(True)

        # Create the FarkasTemplate instance with the mock TransitionSystem
        self.template = ConcreteFarkasTemplate(self.mock_sts, num_templates=2)

        # Reset the template_cnt_init_and_post and template_cnt_trans to None
        # to ensure they're set by the method under test
        self.template.template_cnt_init_and_post = None
        self.template.template_cnt_trans = None

    def test_add_template_cnts_calls_create_methods(self):
        """Test that add_template_cnts calls the create methods."""
        # Create mock return values for the create methods
        mock_init_constraints = BoolVal(True)
        mock_trans_constraints = BoolVal(True)
        mock_post_constraints = BoolVal(True)

        # Mock the create methods
        with patch.object(self.template, '_create_init_constraints',
                          return_value=mock_init_constraints) as mock_create_init:
            with patch.object(self.template, '_create_trans_constraints',
                              return_value=mock_trans_constraints) as mock_create_trans:
                with patch.object(self.template, '_create_post_constraints',
                                  return_value=mock_post_constraints) as mock_create_post:
                    # Call the method under test
                    self.template.add_template_cnts()

                    # Verify that the create methods were called
                    mock_create_init.assert_called_once()
                    mock_create_trans.assert_called_once()
                    mock_create_post.assert_called_once()

    def test_add_template_cnts_sets_template_cnt_fields(self):
        """Test that add_template_cnts sets the template_cnt fields correctly."""
        # Create mock return values for the create methods
        mock_init_constraints = BoolVal(True)
        mock_trans_constraints = BoolVal(True)
        mock_post_constraints = BoolVal(True)

        # Mock the create methods
        with patch.object(self.template, '_create_init_constraints', return_value=mock_init_constraints):
            with patch.object(self.template, '_create_trans_constraints', return_value=mock_trans_constraints):
                with patch.object(self.template, '_create_post_constraints', return_value=mock_post_constraints):
                    # Call the method under test
                    self.template.add_template_cnts()

                    # Verify that the template_cnt fields were set correctly
                    self.assertEqual(self.template.template_cnt_init_and_post,
                                     And(mock_init_constraints, mock_post_constraints))
                    self.assertEqual(self.template.template_cnt_trans, mock_trans_constraints)

    def test_add_template_cnts_with_real_create_methods(self):
        """Test add_template_cnts with real create methods."""
        # Mock the apply_farkas_lemma method to return a simple constraint
        mock_farkas_constraints = [BoolVal(True)]

        with patch.object(FarkasLemma, 'apply_farkas_lemma', return_value=mock_farkas_constraints):
            # Call the method under test
            self.template.add_template_cnts()

            # Verify that the template_cnt fields were set
            self.assertIsNotNone(self.template.template_cnt_init_and_post)
            self.assertIsNotNone(self.template.template_cnt_trans)

    def test_add_template_cnts_integration(self):
        """Integration test for add_template_cnts."""
        # Create a simple TransitionSystem for testing
        sts = Mock(spec=TransitionSystem)
        x = Real('x')
        x_prime = Real('x_prime')
        sts.variables = [x]
        sts.prime_variables = [x_prime]
        sts.init = x == 0
        sts.trans = x_prime == x + 1
        sts.post = x >= 0

        # Create the FarkasTemplate instance
        template = FarkasTemplate(sts, num_templates=1)

        # Mock the apply_farkas_lemma method to return a simple constraint
        mock_farkas_constraints = [BoolVal(True)]

        with patch.object(FarkasLemma, 'apply_farkas_lemma', return_value=mock_farkas_constraints):
            # Call the method under test
            template.add_template_cnts()

            print(template.template_cnt_trans)

            # Verify that the template_cnt fields were set
            self.assertIsNotNone(template.template_cnt_init_and_post)
            self.assertIsNotNone(template.template_cnt_trans)

            # Verify that the constraints are of the expected type
            # Use is_and() instead of isinstance() with And
            self.assertTrue(is_and(template.template_cnt_init_and_post))
            self.assertEqual(template.template_cnt_trans, And(mock_farkas_constraints))

    def test_add_template_cnts_with_empty_constraints(self):
        """Test add_template_cnts with empty constraints."""
        # Mock the create methods to return empty constraints
        with patch.object(self.template, '_create_init_constraints', return_value=BoolVal(True)):
            with patch.object(self.template, '_create_trans_constraints', return_value=BoolVal(True)):
                with patch.object(self.template, '_create_post_constraints', return_value=BoolVal(True)):
                    # Call the method under test
                    self.template.add_template_cnts()

                    # Verify that the template_cnt fields were set correctly
                    self.assertEqual(self.template.template_cnt_init_and_post, And(BoolVal(True), BoolVal(True)))
                    self.assertEqual(self.template.template_cnt_trans, BoolVal(True))


if __name__ == '__main__':
    # Replace the default test runner with one that doesn't buffer output
    unittest.main(buffer=False)
