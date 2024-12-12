from typing import Optional

import z3

from efmc.utils import get_variables


def qe_abduce(pre_cond: z3.BoolRef, post_cond: z3.BoolRef) -> Optional[z3.ExprRef]:
    """
    Performs abduction using quantifier elimination.

    Computes ψ by eliminating variables from Γ -> φ that aren't in the target vocabulary.

    Args:
        pre_cond: Precondition Γ
        post_cond: Postcondition φ

    Returns:
        Optional[z3.ExprRef]: The abduced formula ψ if successful, None otherwise

    Example:
        pre: x ≤ 0 ∧ y > 1
        post: 2x − y + 3z ≤ 10
        Returns formula over z (vars in post but not in pre)
    """
    try:
        aux_fml = z3.Implies(pre_cond, post_cond)

        # Variables to keep: those in post but not in pre
        post_vars_minus_pre_vars = set(get_variables(post_cond)) - set(get_variables(pre_cond))

        # Variables to eliminate: all others
        vars_to_forget = set(get_variables(aux_fml)) - post_vars_minus_pre_vars

        if not vars_to_forget:
            return aux_fml

        qfml = z3.ForAll(list(vars_to_forget), aux_fml)
        qe_result = z3.Tactic("qe2").apply(qfml)

        if qe_result and len(qe_result) > 0:
            return qe_result[0].as_expr()
        return None

    except z3.Z3Exception as e:
        print(f"QE abduction failed: {e}")
        return None
