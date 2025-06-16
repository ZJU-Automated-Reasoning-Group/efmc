"""
FIXME: Generating aux invariants for k-induction (not implemented)
- Template-based invariant generation
- Houdini
"""
import z3

from efmc.engines.ef.ef_prover import EFProver
from efmc.sts import TransitionSystem


class InvariantGenerator(object):

    def __init__(self, sts: TransitionSystem):
        """Init"""
        self.sts = sts

    def generate_via_ef(self):
        """Using exists-forall solving to generate aux invariants"""
        ef_prover = EFProver(self.sts, validate_invariant=True)
        ef_prover.ignore_post_cond = True  # an important flag
        ef_prover.validate_invariant = False  # do not check the invariant after generating.
        if self.sts.has_bv:
            ef_prover.set_template("bv_interval")
        else:
            ef_prover.set_template("power_interval")
        if ef_prover.solve():
            if hasattr(ef_prover, 'inductive_invaraint') and ef_prover.inductive_invaraint is not None:
                if z3.is_true(z3.simplify(ef_prover.inductive_invaraint)):
                    return z3.BoolVal(True)  # the invariant is too weak (True)
                return ef_prover.inductive_invaraint
            return z3.BoolVal(True)  # No invariant was generated
        else:
            return z3.BoolVal(True)
