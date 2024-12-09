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

from typing import Optional

import z3

from efmc.engines.abduction.mistral_z3 import MSASolver
from efmc.utils import is_sat, is_entail, get_variables


def check_abduct(pre_cond: z3.BoolRef, post_cond: z3.BoolRef,
                 abdcut: z3.BoolRef) -> bool:
    """
    Validates an abductive solution by checking consistency and sufficiency.

    Args:
        pre_cond: Precondition Γ
        post_cond: Postcondition φ
        abdcut: Candidate abduction ψ

    Returns:
        bool: True if abdcut is a valid abduction, False otherwise
    """
    # Check consistency: Γ ∧ ψ is satisfiable
    if not is_sat(z3.And(pre_cond, abdcut)):
        return False

    # Check sufficiency: Γ ∧ ψ |= φ
    if not is_entail(z3.And(pre_cond, abdcut), post_cond):
        return False

    return True


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


def abduce(pre_cond: z3.BoolRef, post_cond: z3.BoolRef) -> Optional[z3.ExprRef]:
    """
    Main abduction function that attempts both QE and Dillig approaches.

    Args:
        pre_cond: Precondition Γ
        post_cond: Postcondition φ

    Returns:
        Optional[z3.ExprRef]: The abduced formula ψ if successful, None otherwise
    """
    # Try QE-based abduction first
    result = qe_abduce(pre_cond, post_cond)
    if result is not None:
        return result

    # Fall back to Dillig-style abduction
    return dillig_abduce(pre_cond, post_cond)


def demo_abduct():
    """
    Test cases for the abduction implementation.
    """
    x, y, z = z3.Ints('x y z')

    test_cases = [
        # Test case 1: Simple linear constraints
        {
            'pre': z3.And(x <= 0, y > 1),
            'post': 2 * x - y + 3 * z <= 10,
            'expected_success': True
        },

        # Test case 2: More complex constraints
        {
            'pre': z3.And(x >= 0, y >= 0),
            'post': x + y + z <= 5,
            'expected_success': True
        },

        # Test case 3: Unsatisfiable case
        {
            'pre': z3.And(x > 0, x < 0),
            'post': z == 0,
            'expected_success': False
        },

        # Test case 4: Non-linear constraints
        {
            'pre': x * x <= 4,
            'post': z >= -2,
            'expected_success': True
        }
    ]

    for i, test in enumerate(test_cases, 1):
        print(f"\nTest case {i}:")
        print(f"Pre-condition: {test['pre']}")
        print(f"Post-condition: {test['post']}")

        result = abduce(test['pre'], test['post'])
        success = result is not None

        print(f"Result: {result}")
        print(f"Success: {success}")
        print(f"Expected success: {test['expected_success']}")
        print(f"Test {'passed' if success == test['expected_success'] else 'failed'}")

        if result is not None:
            print("Verification:")
            print(f"Consistent: {is_sat(z3.And(test['pre'], result))}")
            print(f"Sufficient: {is_entail(z3.And(test['pre'], result), test['post'])}")


if __name__ == "__main__":
    demo_abduct()
