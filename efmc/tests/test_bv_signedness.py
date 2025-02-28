from efmc.tests import main
from efmc.utils.bv_utils import get_signedness, Signedness
import z3


def test_get_signedness():
    # Test unsigned comparisons
    x = z3.BitVec("x", 32)
    y = z3.BitVec("y", 32)
    
    # BVULT (unsigned less than)
    formula = z3.BVULT(x, y)
    assert get_signedness(formula) == Signedness.UNSIGNED
    
    # BVULE (unsigned less than or equal)
    formula = z3.BVULE(x, y)
    assert get_signedness(formula) == Signedness.UNSIGNED
    
    # BVUGT (unsigned greater than)
    formula = z3.BVUGT(x, y)
    assert get_signedness(formula) == Signedness.UNSIGNED
    
    # BVUGE (unsigned greater than or equal)
    formula = z3.BVUGE(x, y)
    assert get_signedness(formula) == Signedness.UNSIGNED

    # Test signed comparisons
    # BVSLT (signed less than)
    formula = z3.BVSLT(x, y)
    assert get_signedness(formula) == Signedness.SIGNED
    
    # BVSLE (signed less than or equal)
    formula = z3.BVSLE(x, y)
    assert get_signedness(formula) == Signedness.SIGNED
    
    # BVSGT (signed greater than)
    formula = z3.BVSGT(x, y)
    assert get_signedness(formula) == Signedness.SIGNED
    
    # BVSGE (signed greater than or equal)
    formula = z3.BVSGE(x, y)
    assert get_signedness(formula) == Signedness.SIGNED

    # Test operations with unknown signedness
    # Addition
    formula = z3.BVADD(x, y)
    assert get_signedness(formula) == Signedness.UNKNOWN
    
    # Multiplication
    formula = z3.BVMUL(x, y)
    assert get_signedness(formula) == Signedness.UNKNOWN
    
    # Bitwise AND
    formula = x & y
    assert get_signedness(formula) == Signedness.UNKNOWN

    # Test nested operations
    # Signed operation within arithmetic
    formula = z3.BVADD(z3.BVSLT(x, y), z3.BitVecVal(1, 32))
    assert get_signedness(formula) == Signedness.SIGNED
    
    # Unsigned operation within arithmetic
    formula = z3.BVMUL(z3.BVULT(x, y), z3.BitVecVal(1, 32))
    assert get_signedness(formula) == Signedness.UNSIGNED


if __name__ == "__main__":
    main()
