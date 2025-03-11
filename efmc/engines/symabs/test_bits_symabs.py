"""
Test script for bit-level symbolic abstractions.
"""

import z3
import z3.z3util
import logging

from efmc.engines.symabs.bits_symabs import BitSymbolicAbstraction, strongest_consequence
from efmc.utils.z3_solver_utils import is_entail

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


def test_known_bits():
    """Test the known bits abstraction"""
    # Create a simple formula where some bits are fixed
    x = z3.BitVec('x', 8)
    y = z3.BitVec('y', 8)
    
    # x & 0x0F == 0x0A (fixes the lower 4 bits of x)
    # y == x + 1 (relates y to x)
    fml = z3.And(x & 0x0F == 0x0A, y == x + 1)
    
    # Compute the strongest consequence in the known bits domain
    result = strongest_consequence(fml, "known_bits")
    
    logger.info(f"Original formula: {fml}")
    logger.info(f"Known bits abstraction: {result}")
    
    # Check that the result is indeed a consequence
    assert is_entail(fml, result)
    
    # Create a BitSymbolicAbstraction object to inspect the known bits
    symabs = BitSymbolicAbstraction()
    symabs.init_from_fml(fml)
    symabs.known_bits_abs()
    
    # Print the known bits for each variable
    for var, bits in symabs.known_bits.items():
        logger.info(f"Known bits for {var}:")
        for i, (must_be_0, must_be_1) in enumerate(bits):
            if must_be_0:
                logger.info(f"  Bit {i} must be 0")
            elif must_be_1:
                logger.info(f"  Bit {i} must be 1")
            else:
                logger.info(f"  Bit {i} is unknown")


def test_bit_predicates():
    """Test the bit predicates abstraction"""
    # Create a simple formula with bit-level relationships
    x = z3.BitVec('x', 8)
    y = z3.BitVec('y', 8)
    
    # y == x ^ 0xFF (y is the bitwise complement of x)
    fml = y == x ^ 0xFF
    
    # Compute the strongest consequence in the bit predicates domain
    result = strongest_consequence(fml, "bit_predicates")
    
    logger.info(f"Original formula: {fml}")
    logger.info(f"Bit predicates abstraction: {result}")
    
    # Check that the result is indeed a consequence
    assert is_entail(fml, result)
    
    # Create a BitSymbolicAbstraction object to inspect the bit predicates
    symabs = BitSymbolicAbstraction()
    symabs.init_from_fml(fml)
    symabs.bit_predicates_abs()
    
    # Print the bit predicates
    logger.info("Bit predicates:")
    for i, pred in enumerate(symabs.bit_predicates):
        logger.info(f"  {i+1}. {pred}")


def test_combined():
    """Test the combined bit-level abstractions"""
    # Create a formula with both fixed bits and bit-level relationships
    x = z3.BitVec('x', 8)
    y = z3.BitVec('y', 8)
    z = z3.BitVec('z', 8)
    
    # x & 0xF0 == 0x30 (fixes the upper 4 bits of x)
    # y == x | 0x0F (sets the lower 4 bits of y to 1)
    # z == x & y (z is the bitwise AND of x and y)
    fml = z3.And(x & 0xF0 == 0x30, y == x | 0x0F, z == x & y)
    
    # Compute the strongest consequence in all bit-level domains
    result = strongest_consequence(fml, "all")
    
    logger.info(f"Original formula: {fml}")
    logger.info(f"Combined bit-level abstraction: {result}")
    
    # Check that the result is indeed a consequence
    assert is_entail(fml, result)


if __name__ == "__main__":
    logger.info("Testing known bits abstraction...")
    test_known_bits()
    
    logger.info("\nTesting bit predicates abstraction...")
    test_bit_predicates()
    
    logger.info("\nTesting combined bit-level abstractions...")
    test_combined()
    
    logger.info("\nAll tests passed!") 