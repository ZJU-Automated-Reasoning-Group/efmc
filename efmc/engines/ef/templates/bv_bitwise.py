"""
FIXME: generated by LLM, to be reviewed

For examples, 
1. The knowbits domain tracks must-information about individual bits (0, 1, or unknown).
2. The predicate abstracion domain over single bits of a bit-vecor (we treat each bit of the bit-vector as a "predicate"?, which seems interesting)
   Related: tmplate-based xx over predicate abstraction domain? (it seems that Sumit Gulwani has a related work)
3. The reduced product of xxxx?

Also refer to the abstract domains in Oh's PLDI 23 program synthesis paper?
"""

from efmc.engines.ef.templates.abstract_template import TemplateType, Template
from efmc.sts import TransitionSystem
from efmc.utils import get_variables, big_and
import z3


class KnownBitsTemplate(Template):
    """
    Known bits abstract domain for bit-vectors.
    
    For each bit position in each bit-vector variable, this domain tracks whether
    the bit must be 0, must be 1, or is unknown. This allows precise tracking of
    bit-level operations like bitwise AND, OR, XOR, etc.
    """
    def __init__(self, ts: TransitionSystem):
        self.template_type = TemplateType.BV_KNOWNBITS
        self.sts = ts
        self.bit_correlations = []  # Initialize to empty list
        
        # Initialize template variables and constraints
        self.add_template_vars()
        
        # Pre-compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()
        
    def add_template_vars(self):
        # Store the original Z3 variables
        self.template_vars = self.sts.variables.copy()
        self.bit_vars = {}
        
        # For each variable and each bit position, create two Boolean variables
        # to represent must-be-0 and must-be-1
        for i, var in enumerate(self.template_vars):
            if z3.is_bv(var):
                var_name = str(var)
                bw = var.size()
                self.bit_vars[i] = [(z3.Bool(f"must0_{var_name}_{j}"), 
                                   z3.Bool(f"must1_{var_name}_{j}")) 
                                  for j in range(bw)]

    def get_additional_cnts_for_template_vars(self):
        cnts = []
        # A bit cannot be must-be-0 and must-be-1 at the same time
        for var_idx in self.bit_vars:
            for must0, must1 in self.bit_vars[var_idx]:
                cnts.append(z3.Not(z3.And(must0, must1)))
        return z3.And(cnts) if cnts else z3.BoolVal(True)
    
    def add_template_cnts(self):
        """
        Add constraints to the template variables.
        """
        # Constraints for original variables
        cnts = []
        for var_idx in self.bit_vars:
            var = self.template_vars[var_idx]
            for j, (must0, must1) in enumerate(self.bit_vars[var_idx]):
                # Extract j-th bit
                bit_j = z3.Extract(j, j, var)
                # If must0 is true, bit must be 0
                cnts.append(z3.Implies(must0, bit_j == 0))
                # If must1 is true, bit must be 1
                cnts.append(z3.Implies(must1, bit_j == 1))
        
        # Store constraints for original variables
        self.template_cnt_init_and_post = z3.And(cnts) if cnts else z3.BoolVal(True)
        
        # Constraints for primed variables (for transition relation)
        cnts_prime = []
        for var_idx in self.bit_vars:
            var_prime = self.sts.prime_variables[var_idx]
            for j, (must0, must1) in enumerate(self.bit_vars[var_idx]):
                # Extract j-th bit
                bit_j = z3.Extract(j, j, var_prime)
                # If must0 is true, bit must be 0
                cnts_prime.append(z3.Implies(must0, bit_j == 0))
                # If must1 is true, bit must be 1
                cnts_prime.append(z3.Implies(must1, bit_j == 1))
        
        # Store constraints for primed variables
        self.template_cnt_trans = z3.And(cnts_prime) if cnts_prime else z3.BoolVal(True)

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """
        Build an invariant from a model by fixing the values of template variables.
        
        Args:
            model: Z3 model containing values for template variables
            use_prime_variables: Whether to use primed variables in the invariant
        
        Returns:
            Z3 expression representing the invariant
        """
        cnts = []
        for var_idx in self.bit_vars:
            var = self.sts.prime_variables[var_idx] if use_prime_variables else self.template_vars[var_idx]
            for j, (must0, must1) in enumerate(self.bit_vars[var_idx]):
                if z3.is_true(model.eval(must0)):
                    bit_j = z3.Extract(j, j, var)
                    cnts.append(bit_j == 0)
                elif z3.is_true(model.eval(must1)):
                    bit_j = z3.Extract(j, j, var)
                    cnts.append(bit_j == 1)
        return big_and(cnts) if cnts else z3.BoolVal(True)


class BitPredAbsTemplate(Template):
    """
    Predicate abstraction domain over individual bits of bit-vector variables.
    
    This domain treats each bit of a bit-vector as a predicate and allows
    Boolean combinations of these predicates to form invariants. It's useful
    for capturing complex bit-level properties that can't be expressed by
    the known bits domain alone.
    """
    def __init__(self, ts: TransitionSystem, **kwargs):
        self.template_type = TemplateType.BV_BITS_PREDICATE_ABSTRACTION
        self.sts = ts
        self.num_predicates = kwargs.get("num_predicates", 5)
        
        # Initialize template variables and constraints
        self.add_template_vars()
        
        # Pre-compute to reduce redundant calling
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        self.add_template_cnts()
        
    def add_template_vars(self):
        self.template_vars = self.sts.variables.copy()
        self.bit_preds = []
        self.pred_vars = []
        
        # Create Boolean variables for each predicate
        for i in range(self.num_predicates):
            self.pred_vars.append(z3.Bool(f"pred_{i}"))
            
        # For each bit-vector variable, extract each bit as a potential predicate
        for var in self.template_vars:
            if z3.is_bv(var):
                bw = var.size()
                for i in range(bw):
                    bit_i = z3.Extract(i, i, var) == 1
                    self.bit_preds.append(bit_i)
    
    def get_additional_cnts_for_template_vars(self):
        # No additional constraints needed for template variables
        return z3.BoolVal(True)
    
    def add_template_cnts(self):
        cnts = []
        # For each predicate variable, create a constraint that it equals
        # some Boolean combination of bit predicates
        for pred_var in self.pred_vars:
            # Create selector variables for each bit predicate
            selectors = []
            for i, _ in enumerate(self.bit_preds):
                selectors.append(z3.Bool(f"sel_{pred_var}_{i}"))
                selectors.append(z3.Bool(f"neg_sel_{pred_var}_{i}"))
            
            # A predicate is a disjunction of conjunctions of bit predicates
            disj_terms = []
            for i in range(min(3, len(self.bit_preds))):  # Limit complexity
                conj_terms = []
                for j, bit_pred in enumerate(self.bit_preds):
                    # Either include the predicate, its negation, or neither
                    conj_terms.append(z3.Implies(selectors[j*2], bit_pred))
                    conj_terms.append(z3.Implies(selectors[j*2+1], z3.Not(bit_pred)))
                disj_terms.append(z3.And(conj_terms))
            
            # The predicate variable equals the constructed Boolean combination
            cnts.append(pred_var == z3.Or(disj_terms))
        
        # Store constraints for original variables
        self.template_cnt_init_and_post = big_and(cnts) if cnts else z3.BoolVal(True)
        
        # Constraints for primed variables (for transition relation)
        # Create a substitution map from original to primed variables
        var_subst = {}
        for i, var in enumerate(self.template_vars):
            if z3.is_bv(var):
                var_subst[var] = self.sts.prime_variables[i]
        
        # Apply substitution to create constraints for primed variables
        if var_subst:
            self.template_cnt_trans = z3.substitute(self.template_cnt_init_and_post, 
                                                   [(k, v) for k, v in var_subst.items()])
        else:
            self.template_cnt_trans = self.template_cnt_init_and_post
    
    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables=False):
        """
        Build an invariant from a model by fixing the values of template variables.
        
        Args:
            model: Z3 model containing values for template variables
            use_prime_variables: Whether to use primed variables in the invariant
        
        Returns:
            Z3 expression representing the invariant
        """
        # Substitute variables if needed
        var_subst = {}
        if use_prime_variables:
            for i, var in enumerate(self.template_vars):
                var_subst[var] = self.sts.prime_variables[i]
        
        # Evaluate each predicate in the model
        cnts = []
        for pred_var in self.pred_vars:
            if z3.is_true(model.eval(pred_var)):
                # Find which bit predicates are selected
                pred_expr = z3.BoolVal(False)
                for i, bit_pred in enumerate(self.bit_preds):
                    sel = z3.Bool(f"sel_{pred_var}_{i}")
                    neg_sel = z3.Bool(f"neg_sel_{pred_var}_{i}")
                    
                    if z3.is_true(model.eval(sel)):
                        pred_expr = bit_pred
                        break
                    elif z3.is_true(model.eval(neg_sel)):
                        pred_expr = z3.Not(bit_pred)
                        break
                
                # Apply variable substitution if needed
                if use_prime_variables and var_subst:
                    pred_expr = z3.substitute(pred_expr, [(k, v) for k, v in var_subst.items()])
                
                cnts.append(pred_expr)
        
        return big_and(cnts) if cnts else z3.BoolVal(True)