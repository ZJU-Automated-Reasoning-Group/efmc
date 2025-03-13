"""
FIXME: by LLM, to check.
Compute most-precise (best) bit-level abstractions for bit-vector formulas.


- Known Bits Abstraction: For each bit position of each bit-vector variable, we track whether the bit must be 0, must be 1, or is unknown.
-  Bit Predicates Abstraction: We track relationships between individual bits of different variables, such as equality, negation (XOR), implication, conjunction, and disjunction. (Is this true?)
- Combined Abstraction: We can compute both abstractions together to get a more precise result.

(The full "predicate abstraction domain (the element in the domain is a Boolean combination over a set of Boolean variables)" is not implemented in this code.)

This will be used to compute the strongest consequence of a formula in a given domain. The "strongest consequence" is operation is then used by the symabs_prover to compute the strongest inductive invariant.
"""

import z3
import logging
from typing import Dict, List, Tuple, Set, Optional
from timeit import default_timer as symabs_timer

from efmc.utils.z3_solver_utils import is_entail

logger = logging.getLogger(__name__)


def get_bv_size(x: z3.ExprRef) -> int:
    """Get bit-vector size"""
    if z3.is_bv(x):
        return x.sort().size()
    else:
        return -1


class BitSymbolicAbstraction:
    """
    Symbolic abstraction for bit-level properties of bit-vector formulas.
    
    This class implements two main abstractions:
    1. Known bits: For each bit position, track if it must be 0, must be 1, or unknown
    2. Bit predicates: Track relationships between individual bits
    """
    
    def __init__(self):
        self.initialized = False
        self.formula = z3.BoolVal(True)
        self.vars = []
        self.known_bits_abs_as_fml = z3.BoolVal(True)
        self.bit_predicates_abs_as_fml = z3.BoolVal(True)
        
        # Timeout settings for queries
        self.single_query_timeout = 5000
        self.multi_query_timeout = 10000
        
        # Optimization settings
        self.compact_opt = True
        self.do_simplify = True
        
        # Bit-level information
        self.known_bits = {}  # Maps var -> list of (must_be_0, must_be_1) for each bit
        self.bit_predicates = []  # List of predicates relating bits
        
    def do_simplification(self):
        """Simplify the formula if enabled"""
        if self.do_simplify:
            start = symabs_timer()
            self.formula = z3.simplify(self.formula)
            end = symabs_timer()
            logger.debug(f"Simplification took {end - start:.2f} seconds")
    
    def init_from_fml(self, fml: z3.BoolRef):
        """Initialize from a formula"""
        self.formula = fml
        self.initialized = True
        self.vars = list(set([v for v in z3.z3util.get_vars(fml)]))
        if not self.vars:
            logger.warning("No variables found in formula")
        self.do_simplification()
    
    def min_once(self, exp: z3.ExprRef) -> z3.ExprRef:
        """Find the minimum value of an expression under the formula"""
        if z3.is_bv(exp):
            # For bit-vectors, use optimization
            opt = z3.Optimize()
            opt.set("timeout", self.single_query_timeout)
            opt.add(self.formula)
            
            min_handle = opt.minimize(exp)
            
            if opt.check() == z3.sat:
                try:
                    min_val = opt.lower(min_handle)
                    return z3.BitVecVal(min_val.as_long(), exp.sort().size())
                except z3.Z3Exception as e:
                    logger.warning(f"Z3 exception in min_once: {e}")
            
            # Fallback to a large negative value
            return z3.BitVecVal(0, exp.sort().size())
        else:
            # For non-bit-vectors, return the expression itself
            return exp
    
    def max_once(self, exp: z3.ExprRef) -> z3.ExprRef:
        """Find the maximum value of an expression under the formula"""
        if z3.is_bv(exp):
            # For bit-vectors, use optimization
            opt = z3.Optimize()
            opt.set("timeout", self.single_query_timeout)
            opt.add(self.formula)
            
            max_handle = opt.maximize(exp)
            
            if opt.check() == z3.sat:
                try:
                    max_val = opt.upper(max_handle)
                    return z3.BitVecVal(max_val.as_long(), exp.sort().size())
                except z3.Z3Exception as e:
                    logger.warning(f"Z3 exception in max_once: {e}")
            
            # Fallback to a large positive value
            return z3.BitVecVal((1 << exp.sort().size()) - 1, exp.sort().size())
        else:
            # For non-bit-vectors, return the expression itself
            return exp
    
    def is_bit_must_be_0(self, var: z3.ExprRef, bit_idx: int) -> bool:
        """Check if a specific bit must be 0"""
        if not z3.is_bv(var):
            return False
        
        s = z3.Solver()
        s.set("timeout", self.single_query_timeout)
        s.add(self.formula)
        
        # Check if the bit can be 1
        bit_is_1 = z3.Extract(bit_idx, bit_idx, var) == 1
        s.add(bit_is_1)
        
        result = s.check()
        return result == z3.unsat
    
    def is_bit_must_be_1(self, var: z3.ExprRef, bit_idx: int) -> bool:
        """Check if a specific bit must be 1"""
        if not z3.is_bv(var):
            return False
        
        s = z3.Solver()
        s.set("timeout", self.single_query_timeout)
        s.add(self.formula)
        
        # Check if the bit can be 0
        bit_is_0 = z3.Extract(bit_idx, bit_idx, var) == 0
        s.add(bit_is_0)
        
        result = s.check()
        return result == z3.unsat
    
    def compute_known_bits(self):
        """Compute known bits for all variables"""
        self.known_bits = {}
        
        for var in self.vars:
            if not z3.is_bv(var):
                continue
                
            bv_size = var.sort().size()
            var_known_bits = []
            
            for i in range(bv_size):
                must_be_0 = self.is_bit_must_be_0(var, i)
                must_be_1 = self.is_bit_must_be_1(var, i)
                var_known_bits.append((must_be_0, must_be_1))
            
            self.known_bits[var] = var_known_bits
    
    def known_bits_abs(self):
        """Compute the known bits abstraction"""
        if not self.initialized:
            logger.warning("BitSymbolicAbstraction not initialized")
            return
        
        start = symabs_timer()
        self.compute_known_bits()
        
        # Convert known bits to a formula
        known_bits_cnts = []
        
        for var, bits in self.known_bits.items():
            for i, (must_be_0, must_be_1) in enumerate(bits):
                if must_be_0:
                    known_bits_cnts.append(z3.Extract(i, i, var) == 0)
                elif must_be_1:
                    known_bits_cnts.append(z3.Extract(i, i, var) == 1)
        
        if known_bits_cnts:
            self.known_bits_abs_as_fml = z3.And(*known_bits_cnts)
        else:
            self.known_bits_abs_as_fml = z3.BoolVal(True)
        
        end = symabs_timer()
        logger.debug(f"Known bits abstraction took {end - start:.2f} seconds")
    
    def check_bit_predicate(self, pred: z3.BoolRef) -> bool:
        """Check if a bit predicate is implied by the formula"""
        return is_entail(self.formula, pred)
    
    def generate_bit_predicates(self):
        """Generate potential bit predicates to check"""
        predicates = []
        
        # Only consider bit-vector variables
        bv_vars = [var for var in self.vars if z3.is_bv(var)]
        
        # For each variable, generate predicates for individual bits
        for var in bv_vars:
            bv_size = var.sort().size()
            
            # Add predicates for individual bits
            for i in range(bv_size):
                bit_i = z3.Extract(i, i, var) == 1
                predicates.append(bit_i)
        
        # For pairs of variables with the same bit-width, generate equality predicates
        for i, var1 in enumerate(bv_vars):
            for var2 in bv_vars[i+1:]:
                if var1.sort().size() == var2.sort().size():
                    bv_size = var1.sort().size()
                    
                    # Add predicates for corresponding bits
                    for i in range(bv_size):
                        bit1 = z3.Extract(i, i, var1) == 1
                        bit2 = z3.Extract(i, i, var2) == 1
                        
                        # bit1 == bit2 (equality)
                        predicates.append(bit1 == bit2)
                        
                        # bit1 == ~bit2 (negation/XOR relationship)
                        predicates.append(bit1 == z3.Not(bit2))
                        
                        # bit1 => bit2 (implication)
                        predicates.append(z3.Implies(bit1, bit2))
                        
                        # bit2 => bit1 (reverse implication)
                        predicates.append(z3.Implies(bit2, bit1))
                        
                        # bit1 & bit2 (conjunction)
                        predicates.append(z3.And(bit1, bit2))
                        
                        # bit1 | bit2 (disjunction)
                        predicates.append(z3.Or(bit1, bit2))
        
        return predicates
    
    def bit_predicates_abs(self):
        """Compute the bit predicates abstraction"""
        if not self.initialized:
            logger.warning("BitSymbolicAbstraction not initialized")
            return
        
        start = symabs_timer()
        
        # Generate potential predicates
        potential_predicates = self.generate_bit_predicates()
        
        # Check which predicates are implied by the formula
        valid_predicates = []
        for pred in potential_predicates:
            if self.check_bit_predicate(pred):
                valid_predicates.append(pred)
        
        # Simplify the predicates to remove redundancy
        simplified_predicates = self.simplify_predicates(valid_predicates)
        
        # Convert valid predicates to a formula
        if simplified_predicates:
            self.bit_predicates_abs_as_fml = z3.And(*simplified_predicates)
            self.bit_predicates = simplified_predicates
        else:
            self.bit_predicates_abs_as_fml = z3.BoolVal(True)
            self.bit_predicates = []
        
        end = symabs_timer()
        logger.debug(f"Bit predicates abstraction took {end - start:.2f} seconds")
    
    def simplify_predicates(self, predicates):
        """Simplify a list of predicates by removing redundant ones"""
        if not predicates:
            return []
        
        # First, simplify each predicate
        simplified = [z3.simplify(pred) for pred in predicates]
        
        # Remove duplicates
        unique_preds = []
        str_preds = set()
        
        for pred in simplified:
            pred_str = str(pred)
            if pred_str not in str_preds:
                str_preds.add(pred_str)
                unique_preds.append(pred)
        
        # Check for logical redundancy (if one predicate implies another)
        non_redundant = []
        for i, pred1 in enumerate(unique_preds):
            is_redundant = False
            
            # Skip True and False predicates
            if z3.is_true(pred1) or z3.is_false(pred1):
                continue
                
            for j, pred2 in enumerate(unique_preds):
                if i != j and is_entail(pred2, pred1) and not is_entail(pred1, pred2):
                    # pred2 implies pred1 but not vice versa, so pred1 is weaker
                    is_redundant = True
                    break
            
            if not is_redundant:
                non_redundant.append(pred1)
        
        return non_redundant
    
    def compute_abstraction(self, domain: str = "all"):
        """Compute the abstraction in the specified domain"""
        if not self.initialized:
            logger.warning("BitSymbolicAbstraction not initialized")
            return
        
        if domain in ["known_bits", "all"]:
            self.known_bits_abs()
        
        if domain in ["bit_predicates", "all"]:
            self.bit_predicates_abs()
    
    def get_abstraction_as_fml(self, domain: str = "all") -> z3.BoolRef:
        """Get the abstraction as a formula"""
        if domain == "known_bits":
            return self.known_bits_abs_as_fml
        elif domain == "bit_predicates":
            return self.bit_predicates_abs_as_fml
        elif domain == "all":
            return z3.And(self.known_bits_abs_as_fml, self.bit_predicates_abs_as_fml)
        else:
            logger.warning(f"Unknown domain: {domain}")
            return z3.BoolVal(True)


def strongest_consequence(fml: z3.ExprRef, domain: str = "all") -> z3.ExprRef:
    """
    Compute the strongest consequence of a formula in the bit-level domain.
    
    Args:
        fml: The formula to abstract
        domain: The abstract domain to use ("known_bits", "bit_predicates", or "all")
        
    Returns:
        A formula representing the strongest consequence in the specified domain
    """
    # Create a symbolic abstraction object
    symabs = BitSymbolicAbstraction()
    
    # Initialize with the formula
    symabs.init_from_fml(fml)
    
    # Compute the abstraction
    symabs.compute_abstraction(domain)
    
    # Return the abstraction as a formula
    return symabs.get_abstraction_as_fml(domain)


def test():
    """Test the bit-level symbolic abstraction"""
    # Create a simple formula
    x = z3.BitVec('x', 8)
    y = z3.BitVec('y', 8)
    
    # x & 0x0F == 0x0A
    fml = z3.And(x & 0x0F == 0x0A, y == x + 1)
    
    # Compute the strongest consequence
    result = strongest_consequence(fml)
    
    print("Original formula:", fml)
    print("Strongest consequence:", result)
    
    # Check that the result is indeed a consequence
    assert is_entail(fml, result)
    
    print("Test passed!")


if __name__ == "__main__":
    test()
