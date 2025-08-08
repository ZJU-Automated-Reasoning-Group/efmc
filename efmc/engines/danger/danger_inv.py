"""
Danger invariant checker for transition systems.

This module provides a Z3-based checker that verifies whether a given
"danger invariant" D(x) together with a ranking function R(x) constitutes
an unsafety witness for a transition system.

Intuition (mirrors the secondorder harness semantics):
  - Base/Reachability: there exists an initial state in D
  - Progress: for any state s in D where the program has not yet violated
    the post-condition, we can take a transition to some s' that stays in D
    and strictly decreases R
  - Exit-Violation (optional with guard): if s is in D and the guard does not
    hold, then the post-condition is violated (a bug is reached)

Note on the guard: if a guard predicate is provided, the progress and exit
conditions are conditioned on it similarly to the secondorder danger harness.
If no guard is provided, the progress condition applies unconditionally to D.
"""

from __future__ import annotations

import logging
from typing import Optional

import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult


logger = logging.getLogger(__name__)


class DangerInvariantProver:
    """
    Verifies danger invariants and ranking functions over a TransitionSystem.

    API:
      - verify(inv, rank, guard=None): returns VerificationResult with is_unsafe
        True if the provided danger predicate and rank verify an unsafety witness
        for the system
    """

    def __init__(self, system: TransitionSystem):
        self.sts = system

    def _prime(self, expr: z3.ExprRef) -> z3.ExprRef:
        """Substitute current variables with primed variables in expr."""
        return z3.substitute(expr, list(zip(self.sts.variables, self.sts.prime_variables)))

    def _rank_cmp(self, r_cur: z3.ExprRef, r_nxt: z3.ExprRef) -> z3.ExprRef:
        """Return strict decrease constraint r_cur > r_nxt with correct sort semantics."""
        # Bit-vectors need signedness-aware comparison
        if self.sts.has_bv:
            # Default to unsigned unless TransitionSystem.signedness is set to "signed"
            if getattr(self.sts, "signedness", "unsigned") == "signed":
                return r_cur > r_nxt
            return z3.UGT(r_cur, r_nxt)
        # Reals/Ints use >
        return r_cur > r_nxt

    def verify(
        self,
        inv: z3.ExprRef,
        rank: z3.ExprRef,
        *,
        guard: Optional[z3.ExprRef] = None,
        require_rank_positive: bool = True,
        solver_timeout_ms: Optional[int] = None,
    ) -> VerificationResult:
        """
        Check danger invariant and ranking function against the system.

        Args:
            inv: danger predicate D(x) over current-state variables
            rank: ranking function R(x) over current-state variables
            guard: optional guard predicate G(x). If provided, progress only
                   applies when G(x) holds; exit-violation applies when ¬G(x)
            require_rank_positive: if True, require R(x) > 0 (or unsigned bv
                   trivial) at progress points
            solver_timeout_ms: optional Z3 solver timeout

        Returns:
            VerificationResult with is_unsafe True iff witness checks succeed.
        """
        vars_cur = self.sts.variables
        vars_nxt = self.sts.prime_variables

        if not vars_cur or not vars_nxt or self.sts.trans is None or self.sts.init is None or self.sts.post is None:
            logger.error("TransitionSystem is not fully initialized (vars/trans/init/post required)")
            return VerificationResult(is_safe=False, invariant=None, is_unknown=True)

        # 1) Base/Reachability: ∃x. init(x) ∧ D(x)
        base_formula = z3.Exists(vars_cur, z3.And(self.sts.init, inv))

        # 2) Progress with optional guard: ∀x. (D(x) ∧ (guard(x) or True) ∧ post(x)) ⇒ ∃x'. trans(x,x') ∧ D(x') ∧ R(x') < R(x) ∧ (R(x) > 0)
        inv_prime = self._prime(inv)
        rank_cur = rank
        rank_nxt = self._prime(rank)
        rank_decrease = self._rank_cmp(rank_cur, rank_nxt)
        if self.sts.has_bv and getattr(self.sts, "signedness", "unsigned") == "unsigned":
            # Unsigned BV are always non-negative by semantics
            rank_positive = z3.BoolVal(True)
        else:
            rank_positive = rank_cur > 0 if require_rank_positive else z3.BoolVal(True)

        progress_guard = guard if guard is not None else z3.BoolVal(True)
        progress_ante = z3.And(inv, progress_guard, self.sts.post)
        progress_cons = z3.Exists(
            vars_nxt,
            z3.And(self.sts.trans, inv_prime, rank_decrease, rank_positive),
        )
        progress_formula = z3.ForAll(vars_cur, z3.Implies(progress_ante, progress_cons))

        # 3) Exit-violation (only meaningful if a guard is supplied):
        #    ∀x. (D(x) ∧ ¬guard(x)) ⇒ ¬post(x)
        if guard is not None:
            exit_formula = z3.ForAll(vars_cur, z3.Implies(z3.And(inv, z3.Not(guard)), z3.Not(self.sts.post)))
        else:
            exit_formula = z3.BoolVal(True)

        s = z3.Solver()
        if solver_timeout_ms is not None:
            s.set(timeout=solver_timeout_ms)

        s.add(base_formula)
        s.add(progress_formula)
        s.add(exit_formula)

        res = s.check()
        if res == z3.sat:
            # We consider the system unsafe witnessed by the provided (inv, rank)
            mdl = s.model()
            return VerificationResult(is_safe=False, invariant=inv, counterexample=mdl)
        if res == z3.unknown:
            logger.warning("Danger invariant check returned unknown from Z3")
            return VerificationResult(is_safe=False, invariant=None, is_unknown=True)

        # UNSAT: The provided witness is insufficient/inconsistent
        return VerificationResult(is_safe=True, invariant=None, is_unknown=True)


__all__ = ["DangerInvariantProver"]

