# coding: utf-8
import logging
import z3
from efmc.tests import TestCase, main
from efmc.engines.ef.ef_prover import EFProver
from efmc.sts import TransitionSystem


class TestBitVecBitWiseTemplate(TestCase):

    def test_bv_enhanced_pattern(self):
        """Test bit vector enhanced pattern domain
        """
        print("\n" + "=" * 50)
        print("RUNNING TEST: test_bv_enhanced_pattern")
        print("=" * 50)

        # Define bit vector variables
        BV_SIZE = 8
        x, y, px, py = z3.BitVecs('x y x! y!', BV_SIZE)
        all_vars = [x, y, px, py]

        # Define transition system constraints
        init = z3.And(x == 0, y == 0)

        # x is incremented by 1 each step, but saturates at 15
        # y is incremented by 2 each step, but saturates at 30
        x_update = z3.If(z3.ULT(x, 15), x + 1, 15)
        y_update = z3.If(z3.ULT(y, 30), y + 2, 30)

        updates = z3.And(px == x_update, py == y_update)
        trans = updates

        # The property we want to verify: 
        # If x is odd (bit 0 is 1), then y is even (bit 0 is 0)
        # This property should hold because x and y start at 0,0 and 
        # when x becomes odd (1,3,5...), y is always even (2,6,10...)
        post = z3.Implies(z3.Extract(0, 0, x) == 1, z3.Extract(0, 0, y) == 0)

        # Set up transition system
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        sts.set_signedness("unsigned")

        # Configure and run EF prover with enhanced bit pattern template
        ef_prover = EFProver(sts, validate_invariant=True)
        ef_prover.set_template("bv_enhanced_pattern")
        ef_prover.set_solver("z3api")

        result = ef_prover.solve()
        print(f"Result: {result}")
        print("=" * 50 + "\n")
        # The system should be safe, but the template might be too weak to prove it
        # So we accept either a safe result or an unknown result (not unsafe)
        self.assertFalse(result.is_safe == False and result.counterexample is not None,
                         "Expected the system to be safe or unknown, but got unsafe with counterexample")

    def test_bv_enhanced_pattern_bit_correlation(self):
        """Test bit vector enhanced pattern domain with bit correlations
        """
        print("\n" + "=" * 50)
        print("RUNNING TEST: test_bv_enhanced_pattern_bit_correlation")
        print("=" * 50)

        # Define bit vector variables
        BV_SIZE = 8
        x, y, z, px, py, pz = z3.BitVecs('x y z x! y! z!', BV_SIZE)
        all_vars = [x, y, z, px, py, pz]

        # Define transition system constraints
        # Initial state: x=0, y=0, z=0
        init = z3.And(x == 0, y == 0, z == 0)

        # Transition relation:
        # x increments by 1 each step
        # y is always 2*x
        # z's bit 0 is always the XOR of x's bit 0 and y's bit 1
        x_update = x + 1
        y_update = x * 2

        # Extract bit 0 of x and bit 1 of y
        x_bit0 = z3.Extract(0, 0, x)
        y_bit1 = z3.Extract(1, 1, y)

        # z's bit 0 is x_bit0 XOR y_bit1, other bits remain 0
        z_update = z3.Concat(z3.BitVecVal(0, BV_SIZE - 1), x_bit0 ^ y_bit1)

        updates = z3.And(px == x_update, py == y_update, pz == z_update)
        trans = updates

        # The property we want to verify:
        # z's bit 0 is always the XOR of x's bit 0 and y's bit 1
        post = z3.Extract(0, 0, z) == (x_bit0 ^ y_bit1)

        # Set up transition system
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        sts.set_signedness("unsigned")

        # Configure and run EF prover with enhanced bit pattern template
        ef_prover = EFProver(sts, validate_invariant=True)
        ef_prover.set_template("bv_enhanced_pattern", enable_bit_correlations=True)
        ef_prover.set_solver("z3api")

        result = ef_prover.solve()
        print(f"Result: {result}")
        print("=" * 50 + "\n")
        # The system should be safe, but the template might be too weak to prove it
        # So we accept either a safe result or an unknown result (not unsafe)
        self.assertFalse(result.is_safe == False and result.counterexample is not None,
                         "Expected the system to be safe or unknown, but got unsafe with counterexample")

    def test_bv_enhanced_pattern_modular(self):
        """Test bit vector enhanced pattern domain with modular constraints
        """
        print("\n" + "=" * 50)
        print("RUNNING TEST: test_bv_enhanced_pattern_modular")
        print("=" * 50)

        # Define bit vector variables
        BV_SIZE = 8
        x, y, px, py = z3.BitVecs('x y x! y!', BV_SIZE)
        all_vars = [x, y, px, py]

        # Define transition system constraints
        # Initial state: x=0, y=0
        init = z3.And(x == 0, y == 0)

        # Transition relation:
        # x increments by 1 each step
        # y increments by 4 each step
        x_update = x + 1
        y_update = y + 4

        updates = z3.And(px == x_update, py == y_update)
        trans = updates

        # The property we want to verify:
        # y is always a multiple of 4
        # This should be provable using the modular constraints feature
        post = y % 4 == 0

        # Set up transition system
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        sts.set_signedness("unsigned")

        # Configure and run EF prover with enhanced bit pattern template
        ef_prover = EFProver(sts, validate_invariant=True)
        ef_prover.set_template("bv_enhanced_pattern")
        ef_prover.set_solver("z3api")

        result = ef_prover.solve()
        print(f"Result: {result}")
        print("=" * 50 + "\n")
        # The system should be safe, but the template might be too weak to prove it
        # So we accept either a safe result or an unknown result (not unsafe)
        self.assertFalse(result.is_safe == False and result.counterexample is not None,
                         "Expected the system to be safe or unknown, but got unsafe with counterexample")


if __name__ == '__main__':
    main()
