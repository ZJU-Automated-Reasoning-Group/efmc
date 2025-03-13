# coding: utf-8
import logging
import z3
from efmc.tests import TestCase, main
from efmc.engines.ef.ef_prover import EFProver
from efmc.sts import TransitionSystem
from efmc.engines.ef.templates.bv_enhanced_pattern import EnhancedBitPatternTemplate
from efmc.engines.ef.templates.abstract_template import TemplateType


class TestBitVecEnhancedPatternTemplate(TestCase):
    """Test cases for the EnhancedBitPatternTemplate abstract domain."""

    def test_enhanced_pattern_template_creation(self):
        """Test the creation of an EnhancedBitPatternTemplate instance."""
        print("\n" + "="*50)
        print("RUNNING TEST: test_enhanced_pattern_template_creation")
        print("="*50)
        
        # Define bit vector variables
        BV_SIZE = 8
        x, y = z3.BitVecs('x y', BV_SIZE)
        px, py = z3.BitVecs('x! y!', BV_SIZE)
        
        # Create a dictionary mapping variable names to their Z3 expressions
        variables = {'x': x, 'y': y}
        prime_variables = {'x': px, 'y': py}
        all_variables = [x, y, px, py]

        # Define transition system constraints
        init = z3.And(x == 0, y == 0)
        trans = z3.And(px == x + 1, py == y + 2)
        post = z3.Extract(0, 0, y) == 0

        # Set up transition system
        sts = TransitionSystem()
        sts.variables = variables
        sts.prime_variables = prime_variables
        sts.all_variables = all_variables
        sts.init = init
        sts.trans = trans
        sts.post = post
        sts.has_bv = True
        sts.set_signedness("unsigned")
        
        # Create the EnhancedBitPatternTemplate
        template = EnhancedBitPatternTemplate(sts)
        
        # Check that the template was created correctly
        self.assertEqual(template.template_type, TemplateType.BV_ENHANCED_PATTERN)
        self.assertEqual(template.sts, sts)
        
        print("EnhancedBitPatternTemplate creation test passed!")
        print("="*50 + "\n")

    def test_enhanced_pattern_template_vars(self):
        """Test the template variables creation in EnhancedBitPatternTemplate."""
        print("\n" + "="*50)
        print("RUNNING TEST: test_enhanced_pattern_template_vars")
        print("="*50)
        
        # Define bit vector variables
        BV_SIZE = 8
        x, y = z3.BitVecs('x y', BV_SIZE)
        px, py = z3.BitVecs('x! y!', BV_SIZE)
        
        # Create a dictionary mapping variable names to their Z3 expressions
        variables = {'x': x, 'y': y}
        prime_variables = {'x': px, 'y': py}
        all_variables = [x, y, px, py]

        # Define transition system constraints
        init = z3.And(x == 0, y == 0)
        trans = z3.And(px == x + 1, py == y + 2)
        post = z3.Extract(0, 0, y) == 0

        # Set up transition system
        sts = TransitionSystem()
        sts.variables = variables
        sts.prime_variables = prime_variables
        sts.all_variables = all_variables
        sts.init = init
        sts.trans = trans
        sts.post = post
        sts.has_bv = True
        sts.set_signedness("unsigned")
        
        # Create the EnhancedBitPatternTemplate and add template variables
        template = EnhancedBitPatternTemplate(sts)
        
        # Check that template_vars contains entries
        self.assertTrue(len(template.template_vars) > 0)
        
        # Check that bit_patterns was created
        self.assertTrue(hasattr(template, 'bit_patterns'))
        
        # Check that bit_correlations was created
        self.assertTrue(hasattr(template, 'bit_correlations'))
        
        print("EnhancedBitPatternTemplate template_vars test passed!")
        print("="*50 + "\n")

    def test_enhanced_pattern_template_cnts(self):
        """Test the template constraints in EnhancedBitPatternTemplate."""
        print("\n" + "="*50)
        print("RUNNING TEST: test_enhanced_pattern_template_cnts")
        print("="*50)
        
        # Define bit vector variables
        BV_SIZE = 8
        x, y = z3.BitVecs('x y', BV_SIZE)
        px, py = z3.BitVecs('x! y!', BV_SIZE)
        
        # Create a dictionary mapping variable names to their Z3 expressions
        variables = {'x': x, 'y': y}
        prime_variables = {'x': px, 'y': py}
        all_variables = [x, y, px, py]

        # Define transition system constraints
        init = z3.And(x == 0, y == 0)
        trans = z3.And(px == x + 1, py == y + 2)
        post = z3.Extract(0, 0, y) == 0

        # Set up transition system
        sts = TransitionSystem()
        sts.variables = variables
        sts.prime_variables = prime_variables
        sts.all_variables = all_variables
        sts.init = init
        sts.trans = trans
        sts.post = post
        sts.has_bv = True
        sts.set_signedness("unsigned")
        
        # Create the EnhancedBitPatternTemplate
        template = EnhancedBitPatternTemplate(sts)
        
        # Get the template constraints
        template_cnts = template.template_cnt_init_and_post
        
        # Check that the constraints are a Z3 expression
        self.assertTrue(z3.is_expr(template_cnts))
        
        # Create a solver and check that the constraints are satisfiable
        solver = z3.Solver()
        solver.add(template_cnts)
        self.assertEqual(solver.check(), z3.sat)
        
        print("EnhancedBitPatternTemplate template_cnts test passed!")
        print("="*50 + "\n")

    def test_enhanced_pattern_build_invariant(self):
        """Test the build_invariant_expr method of EnhancedBitPatternTemplate."""
        print("\n" + "="*50)
        print("RUNNING TEST: test_enhanced_pattern_build_invariant")
        print("="*50)
        
        # Define bit vector variables
        BV_SIZE = 8
        x, y = z3.BitVecs('x y', BV_SIZE)
        px, py = z3.BitVecs('x! y!', BV_SIZE)
        
        # Create a dictionary mapping variable names to their Z3 expressions
        variables = {'x': x, 'y': y}
        prime_variables = {'x': px, 'y': py}
        all_variables = [x, y, px, py]

        # Define transition system constraints
        init = z3.And(x == 0, y == 0)
        trans = z3.And(px == x + 1, py == y + 2)
        post = z3.Extract(0, 0, y) == 0

        # Set up transition system
        sts = TransitionSystem()
        sts.variables = variables
        sts.prime_variables = prime_variables
        sts.all_variables = all_variables
        sts.init = init
        sts.trans = trans
        sts.post = post
        sts.has_bv = True
        sts.set_signedness("unsigned")
        
        # Create the EnhancedBitPatternTemplate
        template = EnhancedBitPatternTemplate(sts)
        
        # Create a solver and add constraints
        solver = z3.Solver()
        solver.add(template.template_cnt_init_and_post)
        
        # Check if the model is satisfiable
        result = solver.check()
        self.assertEqual(result, z3.sat)
        
        # Get the model
        model = solver.model()
        
        # Build the invariant expression
        inv = template.build_invariant_expr(model)
        
        # Check that the invariant is a Z3 expression
        self.assertTrue(z3.is_expr(inv))
        
        print("EnhancedBitPatternTemplate build_invariant test passed!")
        print("="*50 + "\n")

    def test_ef_prover_with_enhanced_pattern(self):
        """Test using the EFProver with the EnhancedBitPatternTemplate."""
        print("\n" + "="*50)
        print("RUNNING TEST: test_ef_prover_with_enhanced_pattern")
        print("="*50)
        
        # Define bit vector variables
        BV_SIZE = 8
        x, y, px, py = z3.BitVecs('x y x! y!', BV_SIZE)
        all_vars = [x, y, px, py]

        # Define transition system constraints
        init = z3.And(x == 0, y == 0)
        
        # x is incremented by 1 each step
        # y is incremented by 2 each step
        x_update = x + 1
        y_update = y + 2
        
        updates = z3.And(px == x_update, py == y_update)
        trans = updates
        
        # The property we want to verify: 
        # y is always even (bit 0 is 0)
        post = z3.Extract(0, 0, y) == 0

        # Set up transition system
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        sts.set_signedness("unsigned")

        # Configure and run EF prover with EnhancedBitPatternTemplate
        ef_prover = EFProver(sts, validate_invariant=True)
        ef_prover.set_template("bv_enhanced_pattern")
        ef_prover.set_solver("z3api")

        result = ef_prover.solve()
        print(f"Result: {result}")
        print("="*50 + "\n")
        self.assertEqual(result, "sat", "Expected satisfiable result")

    def test_ef_prover_with_bitwise_operations(self):
        """Test using the EFProver with the EnhancedBitPatternTemplate for bitwise operations."""
        print("\n" + "="*50)
        print("RUNNING TEST: test_ef_prover_with_bitwise_operations")
        print("="*50)
        
        # Define bit vector variables
        BV_SIZE = 8
        x, y, z, px, py, pz = z3.BitVecs('x y z x! y! z!', BV_SIZE)
        all_vars = [x, y, z, px, py, pz]

        # Define transition system constraints
        # x = 5 (101 in binary), y = 3 (011 in binary)
        init = z3.And(x == 5, y == 3, z == (x & y))
        
        # x and y remain constant, z is always x & y
        updates = z3.And(px == x, py == y, pz == (px & py))
        trans = updates
        
        # The property we want to verify: 
        # The 2nd bit (index 1) of z is always 0
        # This is true because x has bit 1 as 0, y has bit 1 as 1,
        # so their bitwise AND will have bit 1 as 0
        post = z3.Extract(1, 1, z) == 0

        # Set up transition system
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        sts.set_signedness("unsigned")

        # Configure and run EF prover with EnhancedBitPatternTemplate
        ef_prover = EFProver(sts, validate_invariant=True)
        ef_prover.set_template("bv_enhanced_pattern")
        ef_prover.set_solver("z3api")

        result = ef_prover.solve()
        print(f"Result: {result}")
        print("="*50 + "\n")
        self.assertEqual(result, "sat", "Expected satisfiable result")

    def test_ef_prover_with_shifting(self):
        """Test using the EFProver with the EnhancedBitPatternTemplate for bit shifting."""
        print("\n" + "="*50)
        print("RUNNING TEST: test_ef_prover_with_shifting")
        print("="*50)
        
        # Define bit vector variables
        BV_SIZE = 8
        x, y, px, py = z3.BitVecs('x y x! y!', BV_SIZE)
        all_vars = [x, y, px, py]

        # Define transition system constraints
        init = z3.And(x == 1, y == 0)
        
        # x is left-shifted by 1 bit each step (x << 1)
        # y remains 0
        x_update = x << 1
        y_update = y
        
        updates = z3.And(px == x_update, py == y_update)
        trans = updates
        
        # The property we want to verify: 
        # After the first step, the least significant bit of x is always 0
        # This is true because left-shifting introduces a 0 in the LSB
        post = z3.Implies(x != 1, z3.Extract(0, 0, x) == 0)

        # Set up transition system
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        sts.set_signedness("unsigned")

        # Configure and run EF prover with EnhancedBitPatternTemplate
        ef_prover = EFProver(sts, validate_invariant=True)
        ef_prover.set_template("bv_enhanced_pattern")
        ef_prover.set_solver("z3api")

        result = ef_prover.solve()
        print(f"Result: {result}")
        print("="*50 + "\n")
        self.assertEqual(result, "sat", "Expected satisfiable result")

    def test_ef_prover_with_bit_masking(self):
        """Test using the EFProver with the EnhancedBitPatternTemplate for bit masking."""
        print("\n" + "="*50)
        print("RUNNING TEST: test_ef_prover_with_bit_masking")
        print("="*50)
        
        # Define bit vector variables
        BV_SIZE = 8
        x, y, px, py = z3.BitVecs('x y x! y!', BV_SIZE)
        all_vars = [x, y, px, py]

        # Define transition system constraints
        init = z3.And(x == 0x3F, y == (x & 0xF0))  # 0x3F = 00111111, 0xF0 = 11110000
        
        # x is updated with some complex bit manipulation
        # y is always x with its lower 4 bits masked to 0
        x_update = (x + 1) ^ 0x55  # XOR with 01010101
        y_update = px & 0xF0       # Mask lower 4 bits to 0
        
        updates = z3.And(px == x_update, py == y_update)
        trans = updates
        
        # The property we want to verify: 
        # The lower 4 bits of y are always 0
        post = (y & 0x0F) == 0

        # Set up transition system
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        sts.set_signedness("unsigned")

        # Configure and run EF prover with EnhancedBitPatternTemplate
        ef_prover = EFProver(sts, validate_invariant=True)
        ef_prover.set_template("bv_enhanced_pattern")
        ef_prover.set_solver("z3api")

        result = ef_prover.solve()
        print(f"Result: {result}")
        print("="*50 + "\n")
        self.assertEqual(result, "sat", "Expected satisfiable result")


if __name__ == '__main__':
    main() 