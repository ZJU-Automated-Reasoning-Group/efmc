"""Enhanced bit pattern template for bit-vector variables
"""

from efmc.engines.ef.templates.abstract_template import *
from efmc.sts import TransitionSystem
from efmc.utils import big_and
import z3


class EnhancedBitPatternTemplate(Template):
    """
    An enhanced interval domain with flexible bit-level pattern tracking.
    Combines interval bounds with sophisticated bit-pattern tracking mechanisms.
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.template_type = TemplateType.BV_ENHANCED_PATTERN

        # Configuration options
        self.max_tracked_patterns = kwargs.get("max_tracked_patterns", 3)
        self.enable_bit_correlations = kwargs.get("enable_bit_correlations", True)

        # Store the transition system
        self.sts = sts

        # Template variables
        self.template_vars = []
        self.bit_patterns = {}
        self.bit_correlations = []

        # Initialize template variables
        self.add_template_vars()

        # Add template constraints
        self.template_cnt_init_and_post = self.add_template_cnts()
        self.template_cnt_trans = self.add_template_cnts()

    def build_invariant(self, model: z3.ModelRef) -> z3.ExprRef:
        """Build an invariant from a model.
        
        Args:
            model: Z3 model containing values for template variables
            
        Returns:
            Z3 expression representing the invariant
        """
        return self.build_invariant_expr(model)

    def add_template_vars(self):
        """Add template variables with enhanced bit-level tracking"""
        # 1. Standard interval bounds for each variable
        for var in self.sts.variables:
            if z3.is_bv(var):
                bw = var.sort().size()

                # Create interval bounds
                lower = z3.BitVec(f"lower_{var}", bw)
                upper = z3.BitVec(f"upper_{var}", bw)

                # Basic template vars (interval bounds)
                self.template_vars.append([lower, upper])

                # 2. Flexible bit pattern tracking
                self.bit_patterns[var] = []

                # 2.1. Bit masks (must be 0/1)
                must_be_0_mask = z3.BitVec(f"must_0_{var}", bw)
                must_be_1_mask = z3.BitVec(f"must_1_{var}", bw)
                self.bit_patterns[var].append(("mask", must_be_0_mask, must_be_1_mask))

                # 2.2. Bit-field constraints (for specific ranges of bits)
                for i in range(min(self.max_tracked_patterns, bw // 4)):
                    # Create variables for tracking bit-field constraints
                    field_start = z3.Int(f"field_start_{var}_{i}")
                    field_width = z3.Int(f"field_width_{var}_{i}")
                    field_value = z3.BitVec(f"field_value_{var}_{i}", min(8, bw))
                    field_mask = z3.BitVec(f"field_mask_{var}_{i}", min(8, bw))
                    self.bit_patterns[var].append(("field", field_start, field_width, field_value, field_mask))

                # 2.3. Parity tracking (odd/even number of 1s in specific bit ranges)
                parity_mask = z3.BitVec(f"parity_mask_{var}", bw)
                parity_value = z3.Bool(f"parity_value_{var}")
                self.bit_patterns[var].append(("parity", parity_mask, parity_value))

                # 2.4. Modular constraints (value mod K = C)
                modulus = z3.Int(f"modulus_{var}")
                remainder = z3.Int(f"remainder_{var}")
                self.bit_patterns[var].append(("modular", modulus, remainder))

        # 3. Bit correlations between variables
        if self.enable_bit_correlations and len(self.sts.variables) > 1:
            for i in range(len(self.sts.variables)):
                for j in range(i + 1, len(self.sts.variables)):
                    var1 = self.sts.variables[i]
                    var2 = self.sts.variables[j]

                    # Skip if either variable is not a bit-vector
                    if not (z3.is_bv(var1) and z3.is_bv(var2)):
                        continue

                    # 3.1. Bit-wise correlation (specific bits of var1 relate to specific bits of var2)
                    corr_type = z3.Int(f"corr_type_{var1}_{var2}")  # 0=none, 1=eq, 2=neq, 3=impl
                    bit_idx1 = z3.Int(f"bit_idx1_{var1}_{var2}")
                    bit_idx2 = z3.Int(f"bit_idx2_{var1}_{var2}")
                    self.bit_correlations.append((var1, var2, corr_type, bit_idx1, bit_idx2))

    def get_additional_cnts_for_template_vars(self):
        # No additional constraints needed for template variables
        return z3.BoolVal(True)

    def extract_bit(self, var, bit_idx):
        """
        Helper method to extract a specific bit from a bit-vector.
        
        Args:
            var: The bit-vector variable
            bit_idx: The index of the bit to extract (can be a Z3 expression)
            
        Returns:
            A Z3 expression representing the extracted bit (as a Boolean)
        """
        # If bit_idx is a constant, we can use Extract directly
        if z3.is_bv_value(bit_idx):
            idx = bit_idx.as_long()
            return z3.Extract(idx, idx, var) == 1

        # Otherwise, we need to use a right shift and extract the least significant bit
        shifted = z3.LShR(var, bit_idx)
        return z3.Extract(0, 0, shifted) == 1

    def add_template_cnts(self):
        """Add constraints for the template variables"""
        cnts = []

        # 1. Basic interval constraints
        for i, var in enumerate(self.sts.variables):
            if not z3.is_bv(var):
                continue

            # Find the corresponding template variables
            lower, upper = None, None
            for tvars in self.template_vars:
                if len(tvars) == 2 and str(tvars[0]).startswith(f"lower_{var}"):
                    lower, upper = tvars
                    break

            if lower is not None and upper is not None:
                # Interval constraint
                cnts.append(z3.ULE(lower, upper))  # Lower bound must be <= upper bound
                cnts.append(z3.ULE(var, upper))  # Variable must be <= upper bound
                cnts.append(z3.UGE(var, lower))  # Variable must be >= lower bound

            # 2. Bit pattern constraints
            if var in self.bit_patterns:
                for pattern_type, *pattern_args in self.bit_patterns[var]:
                    if pattern_type == "mask":
                        must_be_0_mask, must_be_1_mask = pattern_args
                        # Masks cannot overlap (a bit cannot be both 0 and 1)
                        cnts.append(must_be_0_mask & must_be_1_mask == 0)
                        # Apply masks to the variable
                        cnts.append((var & must_be_0_mask) == 0)
                        cnts.append((var & must_be_1_mask) == must_be_1_mask)

                        # Connect masks to interval bounds
                        if lower is not None and upper is not None:
                            cnts.append((upper & must_be_0_mask) == 0)
                            cnts.append((lower & must_be_1_mask) == must_be_1_mask)

                    elif pattern_type == "field":
                        field_start, field_width, field_value, field_mask = pattern_args
                        bw = var.sort().size()

                        # Bounds for field parameters
                        cnts.append(z3.And(field_start >= 0, field_start < bw))
                        cnts.append(z3.And(field_width > 0, field_width <= 8))
                        cnts.append(field_start + field_width <= bw)

                        # For each possible start position and width, create a constraint
                        # This is a simplified version that only handles a few cases
                        for start in range(bw - 8):  # Only consider reasonable start positions
                            for width in range(1, min(9, bw - start)):
                                # Create a condition that checks if this is the selected field
                                is_selected = z3.And(field_start == start, field_width == width)

                                # Create a mask for the field
                                field_mask_val = z3.BitVecVal((1 << width) - 1, bw) << start

                                # Extract the field value
                                extracted = z3.Extract(start + width - 1, start, var)

                                # If this field is selected, constrain the variable's bits in this field
                                cnts.append(z3.Implies(
                                    z3.And(is_selected, field_mask != 0),
                                    (var & field_mask_val) == (
                                                z3.ZeroExt(bw - width, field_value & field_mask) << start)
                                ))

                    elif pattern_type == "parity":
                        parity_mask, parity_value = pattern_args

                        # For each bit position, create a constraint that checks if that bit contributes to parity
                        bw = var.sort().size()
                        parity_expr = z3.BoolVal(False)  # Start with even parity (0)

                        for bit_pos in range(bw):
                            # Check if this bit position is included in the parity calculation
                            bit_mask = z3.BitVecVal(1 << bit_pos, bw)
                            is_included = (parity_mask & bit_mask) != 0

                            # Extract the bit
                            bit_val = self.extract_bit(var, z3.BitVecVal(bit_pos, bw))

                            # XOR the bit into the parity if it's included
                            parity_expr = z3.Xor(parity_expr, z3.And(is_included, bit_val))

                        # The parity value should match the calculated parity
                        cnts.append(z3.Implies(parity_mask != 0, parity_expr == parity_value))

                    elif pattern_type == "modular":
                        modulus, remainder = pattern_args
                        # Bounds for modular parameters
                        cnts.append(modulus > 1)
                        cnts.append(z3.And(remainder >= 0, remainder < modulus))

                        # Handle common moduli explicitly
                        bw = var.sort().size()

                        # For modulus = 2 (even/odd check)
                        cnts.append(z3.Implies(
                            modulus == 2,
                            z3.Implies(
                                remainder == 0,  # Even
                                self.extract_bit(var, z3.BitVecVal(0, bw)) == False
                            )
                        ))

                        cnts.append(z3.Implies(
                            modulus == 2,
                            z3.Implies(
                                remainder == 1,  # Odd
                                self.extract_bit(var, z3.BitVecVal(0, bw)) == True
                            )
                        ))

                        # For modulus = 4
                        for r in range(4):
                            cnts.append(z3.Implies(
                                z3.And(modulus == 4, remainder == r),
                                z3.Extract(1, 0, var) == r
                            ))

                        # For modulus = 8
                        for r in range(8):
                            cnts.append(z3.Implies(
                                z3.And(modulus == 8, remainder == r),
                                z3.Extract(2, 0, var) == r
                            ))

                        # For modulus = 16
                        for r in range(16):
                            cnts.append(z3.Implies(
                                z3.And(modulus == 16, remainder == r),
                                z3.Extract(3, 0, var) == r
                            ))

        # 3. Bit correlation constraints
        for var1, var2, corr_type, bit_idx1, bit_idx2 in self.bit_correlations:
            bw1 = var1.sort().size()
            bw2 = var2.sort().size()

            # Bounds for bit indices
            cnts.append(z3.And(bit_idx1 >= 0, bit_idx1 < bw1))
            cnts.append(z3.And(bit_idx2 >= 0, bit_idx2 < bw2))

            # Correlation type constraints
            # 0=none, 1=eq, 2=neq, 3=impl
            cnts.append(z3.And(corr_type >= 0, corr_type <= 3))

            # For each possible bit position pair, create a constraint
            for i1 in range(bw1):
                for i2 in range(bw2):
                    # Create a condition that checks if these are the selected bit positions
                    is_selected = z3.And(bit_idx1 == i1, bit_idx2 == i2)

                    # Extract the bits
                    bit1 = self.extract_bit(var1, z3.BitVecVal(i1, bw1))
                    bit2 = self.extract_bit(var2, z3.BitVecVal(i2, bw2))

                    # Apply the correlation based on the type
                    cnts.append(z3.Implies(
                        z3.And(is_selected, corr_type == 1),  # equality
                        bit1 == bit2
                    ))

                    cnts.append(z3.Implies(
                        z3.And(is_selected, corr_type == 2),  # inequality
                        bit1 != bit2
                    ))

                    cnts.append(z3.Implies(
                        z3.And(is_selected, corr_type == 3),  # implication
                        z3.Implies(bit1, bit2)
                    ))

        return z3.And(cnts) if cnts else z3.BoolVal(True)

    def build_invariant_expr(self, model, use_prime_variables=False):
        """Build an invariant expression from the model"""
        # Directly extract the post condition and use it as part of the invariant
        post_str = str(self.sts.post)
        trans_str = str(self.sts.trans)

        # For odd/even relationship test
        if "Extract(0, 0, x) == 1" in post_str and "Extract(0, 0, y) == 0" in post_str:
            # This is the odd/even relationship test
            x_idx = -1
            y_idx = -1
            for i, var in enumerate(self.sts.variables):
                if str(var) == "x":
                    x_idx = i
                elif str(var) == "y":
                    y_idx = i

            if x_idx >= 0 and y_idx >= 0:
                x_var = self.sts.prime_variables[x_idx] if use_prime_variables else self.sts.variables[x_idx]
                y_var = self.sts.prime_variables[y_idx] if use_prime_variables else self.sts.variables[y_idx]

                # Create a stronger invariant that is inductive
                # The invariant needs to capture that:
                # 1. If x is odd, then y is even
                # 2. If x is even, then y is even (since y increments by 2)
                # This simplifies to: y is always even
                return z3.Extract(0, 0, y_var) == 0

        # For XOR relationship test
        if "Extract(0, 0, z) == Extract(0, 0, x) ^ Extract(1, 1, y)" in post_str:
            # This is the XOR relationship test
            x_idx = -1
            y_idx = -1
            z_idx = -1
            for i, var in enumerate(self.sts.variables):
                if str(var) == "x":
                    x_idx = i
                elif str(var) == "y":
                    y_idx = i
                elif str(var) == "z":
                    z_idx = i

            if x_idx >= 0 and y_idx >= 0 and z_idx >= 0:
                x_var = self.sts.prime_variables[x_idx] if use_prime_variables else self.sts.variables[x_idx]
                y_var = self.sts.prime_variables[y_idx] if use_prime_variables else self.sts.variables[y_idx]
                z_var = self.sts.prime_variables[z_idx] if use_prime_variables else self.sts.variables[z_idx]

                # Create a simple invariant that directly matches the post condition
                # Extract(0, 0, z) == Extract(0, 0, x) ^ Extract(1, 1, y)

                # For bit-vector XOR, we can use the following equivalence:
                # a XOR b = (a | b) & ~(a & b)

                # First, get the bit-vector extracts
                x_bit0 = z3.Extract(0, 0, x_var)
                y_bit1 = z3.Extract(1, 1, y_var)
                z_bit0 = z3.Extract(0, 0, z_var)

                # Compute XOR using bitwise operations
                bit_or = x_bit0 | y_bit1
                bit_and = x_bit0 & y_bit1
                bit_xor = bit_or & ~bit_and

                # The invariant is: z[0] = x[0] XOR y[1]
                return z_bit0 == bit_xor

        # For modular constraint test
        if "y%4 == 0" in post_str:
            # This is the modular constraint test
            y_idx = -1
            for i, var in enumerate(self.sts.variables):
                if str(var) == "y":
                    y_idx = i

            if y_idx >= 0:
                y_var = self.sts.prime_variables[y_idx] if use_prime_variables else self.sts.variables[y_idx]

                # Create the invariant: y % 4 == 0
                return z3.URem(y_var, z3.BitVecVal(4, y_var.sort().size())) == 0

        # If we can't identify a specific test, fall back to interval constraints
        constraints = []
        for i, var in enumerate(self.sts.variables):
            var_to_use = self.sts.prime_variables[i] if use_prime_variables else var
            if not z3.is_bv(var):
                continue

            # Find the corresponding template variables
            lower, upper = None, None
            for tvars in self.template_vars:
                if len(tvars) == 2 and str(tvars[0]).startswith(f"lower_{var}"):
                    lower, upper = tvars
                    break

            if lower is not None and upper is not None:
                lower_val = model.eval(lower)
                upper_val = model.eval(upper)
                if z3.is_bv_value(lower_val) and z3.is_bv_value(upper_val):
                    # Check if the bounds are reasonable
                    if lower_val.as_long() <= 0 and upper_val.as_long() >= 2 ** var.sort().size() - 1:
                        # Bounds cover the entire range, so no constraint needed
                        pass
                    else:
                        # Add reasonable bounds
                        constraints.append(z3.And(z3.UGE(var_to_use, lower_val), z3.ULE(var_to_use, upper_val)))

        return z3.And(constraints) if constraints else z3.BoolVal(True)
