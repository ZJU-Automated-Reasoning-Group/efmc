"""
A few functions for playing with inductive loop invariants


"""
import z3

from efmc.utils.z3_solver_utils import is_entail, is_sat, is_equiv
from efmc.sts import TransitionSystem


def check_invariant(sts: TransitionSystem, inv: z3.ExprRef, inv_in_prime_variables: z3.ExprRef):
    """Check whether the generated invariant is correct"""
    correct = True
    # 1. Init
    if not is_entail(sts.init, inv):
        correct = False
        print("Init wrong!")

    # 2. Inductive
    if not is_entail(z3.And(sts.trans, inv), inv_in_prime_variables):
        correct = False
        print("Inductive wrong!")

    # 3. Post
    if (not sts.ignore_post_cond) and (not is_entail(inv, sts.post)):
        correct = False
        print("Post not good!")

    if not correct:
        print("Init: ", sts.init)
        print("Trans: ", sts.trans)
        print("Post: ", sts.post)
        print("Inv: ", inv)
    else:
        print("Invariant check success!")



def weaken_invariant(inv):
    """"""
    return None

def strengthen_invariant(inv):
    """"""
    return None

