"""Inductive Generalization
One guidance: counterexample-guided inductive generalization, e.g., using counterexamples to induciveness (CIT)

Two directions: weakening and strengthening

Strategies for generization:
- Craig interpolant
- Abductive inference
- Template-based generalization
- ...

Algorithms that may benefit from generalization:
- IC3/DPR
- CEGAR with Craig interpolant
- Trace abstraction
- ...

FIXME: by LLM, to check if the generalization is correct
"""


import logging
import z3

from efmc.utils.z3_solver_utils import is_entail, is_sat, is_equiv
from efmc.utils.z3_expr_utils import get_variables, negate
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


class InductiveGeneralizer:
    """Main class for inductive generalization"""
    
    def __init__(self, sts: TransitionSystem):
        self.sts = sts
        self.logger = logging.getLogger(__name__)
        
    def get_cti(self, inv: z3.ExprRef) -> z3.ModelRef:
        """Get counterexample to induction"""
        inv_prime = z3.substitute(inv, list(zip(self.sts.variables, self.sts.prime_variables)))
        s = z3.Solver()
        s.add(inv)
        s.add(self.sts.trans)
        s.add(z3.Not(inv_prime))
        if s.check() == z3.sat:
            return s.model()
        return None
        
    def get_cex_to_safety(self, inv: z3.ExprRef) -> z3.ModelRef:
        """Get counterexample to safety property"""
        s = z3.Solver()
        s.add(inv)
        s.add(z3.Not(self.sts.post))
        if s.check() == z3.sat:
            return s.model()
        return None
        
    def get_cex_to_init(self, inv: z3.ExprRef) -> z3.ModelRef:
        """Get counterexample to initiation"""
        s = z3.Solver()
        s.add(self.sts.init)
        s.add(z3.Not(inv))
        if s.check() == z3.sat:
            return s.model()
        return None

    def weaken_using_cti(self, inv: z3.ExprRef) -> z3.ExprRef:
        """Weaken invariant using counterexample to induction"""
        cti = self.get_cti(inv)
        if cti is None:
            return inv
            
        # Extract values from CTI
        state_values = []
        for var in self.sts.variables:
            val = cti.eval(var)
            if val is not None:
                state_values.append(var >= val)
                
        weakened = z3.Or(inv, z3.And(state_values))
        if is_entail(weakened, self.sts.post):
            return weakened
        return inv

    def strengthen_using_cex(self, inv: z3.ExprRef) -> z3.ExprRef:
        """Strengthen invariant using counterexample to safety"""
        cex = self.get_cex_to_safety(inv)
        if cex is None:
            return inv
            
        # Extract values from counterexample
        state_values = []
        for var in self.sts.variables:
            val = cex.eval(var)
            if val is not None:
                state_values.append(var <= val)
                
        strengthened = z3.And(inv, z3.Or(state_values))
        if is_entail(self.sts.init, strengthened):
            return strengthened
        return inv

    def generalize_using_interpolant(self, inv: z3.ExprRef) -> z3.ExprRef:
        """Generalize invariant using Craig interpolation"""
        # TODO: Implement interpolant-based generalization
        raise NotImplementedError
        
    def generalize_using_abduction(self, inv: z3.ExprRef) -> z3.ExprRef:
        """Generalize invariant using abductive inference"""
        # TODO: Implement abduction-based generalization
        raise NotImplementedError
        
    def generalize_using_template(self, inv: z3.ExprRef, template_type: str) -> z3.ExprRef:
        """Generalize invariant using templates"""
        # TODO: Implement template-based generalization
        raise NotImplementedError
        
    def generalize_using_pred_abs(self, inv: z3.ExprRef, predicates: list) -> z3.ExprRef:
        """Generalize invariant using predicate abstraction"""
        # TODO: Implement predicate abstraction-based generalization
        raise NotImplementedError


def weaken_invariant(sts: TransitionSystem, inv: z3.ExprRef) -> z3.ExprRef:
    """Legacy function for backward compatibility"""
    generalizer = InductiveGeneralizer(sts)
    return generalizer.weaken_using_cti(inv)

def strengthen_invariant(sts: TransitionSystem, inv: z3.ExprRef) -> z3.ExprRef:
    """Legacy function for backward compatibility"""
    generalizer = InductiveGeneralizer(sts)
    return generalizer.strengthen_using_cex(inv)


