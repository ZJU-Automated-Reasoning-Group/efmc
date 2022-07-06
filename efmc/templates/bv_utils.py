"""
Facilities for bit-vector related staff
"""
from enum import Enum

import z3
from z3 import BitVecVal, Concat, Extract


class Signedness(Enum):
    SIGNED = 0
    UNSIGNED = 1
    UNKNOWN = 2


def zero_extension(formula: z3.BitVecRef, bit_places: int) -> z3.BitVecRef:
    """Set the rest of bits on the left to 0.
    """
    complement = BitVecVal(0, formula.size() - bit_places)
    formula = z3.Concat(complement, (Extract(bit_places - 1, 0, formula)))
    return formula


def one_extension(formula: z3.BitVecRef, bit_places: int):
    """Set the rest of bits on the left to 1.
    """
    complement = BitVecVal(0, formula.size() - bit_places) - 1
    formula = Concat(complement, (Extract(bit_places - 1, 0, formula)))
    return formula


def sign_extension(formula: z3.BitVecRef, bit_places: int) -> z3.BitVecRef:
    """Set the rest of bits on the left to the value of the sign bit.
    """
    sign_bit = Extract(bit_places - 1, bit_places - 1, formula)

    complement = sign_bit
    for _ in range(formula.size() - bit_places - 1):
        complement = Concat(sign_bit, complement)

    formula = Concat(complement, (Extract(bit_places - 1, 0, formula)))
    return formula


def right_zero_extension(formula: z3.BitVecRef, bit_places: int) -> z3.BitVecRef:
    """Set the rest of bits on the right to 0.
    """
    complement = BitVecVal(0, formula.size() - bit_places)
    formula = Concat(Extract(formula.size() - 1,
                             formula.size() - bit_places,
                             formula),
                     complement)
    return formula


def right_one_extension(formula: z3.BitVecRef, bit_places: int) -> z3.BitVecRef:
    """Set the rest of bits on the right to 1.
    """
    complement = BitVecVal(0, formula.size() - bit_places) - 1
    formula = Concat(Extract(formula.size() - 1,
                             formula.size() - bit_places,
                             formula),
                     complement)
    return formula


def right_sign_extension(formula: z3.BitVecRef, bit_places: int) -> z3.BitVecRef:
    """Set the rest of bits on the right to the value of the sign bit.
    """
    sign_bit_position = formula.size() - bit_places
    sign_bit = Extract(sign_bit_position, sign_bit_position, formula)

    complement = sign_bit
    for _ in range(sign_bit_position - 1):
        complement = Concat(sign_bit, complement)

    formula = Concat(Extract(formula.size() - 1,
                             sign_bit_position,
                             formula),
                     complement)
    return formula
