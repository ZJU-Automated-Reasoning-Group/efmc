"""
NOTE: we aim to implement Dillig's abduction-based invariant inference

Given a set of premises Γ and a desired conclusion φ,
abductive inference finds a simple explanation ψ such that
(1) Γ ∧ ψ |= φ, and
(2) ψ is consistent with known premises Γ.

Idea:
- First, Γ ∧ ψ |= φ can be rewritten as ψ |= Γ -> φ.
- Second, we may use universal qe to compute the sufficient condition of Γ -> φ.
"""

import z3

from efmc.engines.abduction.mistral_z3 import MSASolver
from efmc.utils import is_sat, is_entail, get_variables


def check_abduct(pre_cond, post_cond, abdcut):
    """
    Check the solution
    """
    consistent = is_sat(z3.And(pre_cond, abdcut))
    if not consistent:
        return False

    sufficient = is_entail(z3.And(pre_cond, abdcut), post_cond)
    if not sufficient:
        return False

    return True


def qe_abduce(pre_cond: z3.BoolRef, post_cond: z3.BoolRef):
    """
    Example:
    pre: existing precondition  Γ: x ≤ 0 ∧ y > 1
    post: target specification  φ: 2x − y + 3z ≤ 10
       Γ ∧ ψ |= φ can be rewritten as ψ |= Γ -> φ.
       So, we use universal qe to compute the sufficient condition of Γ -> φ.
    """
    aux_fml = z3.Implies(pre_cond, post_cond)
    # {z}
    post_vars_minus_pre_vars = set(get_variables(post_cond)).difference(set(get_variables(pre_cond)))

    # {x, y}
    vars_to_forget = set(get_variables(aux_fml)).difference(post_vars_minus_pre_vars)
    print(vars_to_forget)

    qfml = z3.ForAll(list(vars_to_forget), aux_fml)
    qet = z3.Tactic("qe2")
    after_qe = qet.apply(qfml)[0].as_expr()
    print("After QE: ", after_qe)  # Not(3*z >= 13) ！！！


def dillig_abduce(pre_cond: z3.BoolRef, post_cond: z3.BoolRef) -> z3.ExprRef:
    """
    Dillig-style abduction (which is very expensive)

    Essentially, MSA + qe_abduce??

    a, b, c, d = Ints('a b c d')
    fml = Or(And(a == 3, b == 3), And(a == 1, b == 1, c == 1, d == 1))
    ms = MSASolver()
    ms.init_from_formula(fml)
    print(ms.find_small_model())  # a = 3, b = 3
    """
    msa = MSASolver()
    return post_cond


def abduce(pre_cond: z3.BoolRef, post_cond: z3.BoolRef):
    qe_abduce(pre_cond, post_cond)
    return True
    # return dillig_abduce(pre_cond, post_cond)
