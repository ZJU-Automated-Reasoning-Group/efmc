"""
A few functions for playing with inductive loop invariants
"""
import logging
import z3

from efmc.utils.z3_solver_utils import is_entail, is_sat, is_equiv
from efmc.utils.z3_expr_utils import get_variables, negate
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)

def check_invariant(sts: TransitionSystem, inv: z3.ExprRef, inv_in_prime_variables: z3.ExprRef):
    """Check whether the generated invariant is correct"""
    correct = True

    # TODO: should we check the three conditions all-in-one?

    # 1. Check initiation: inv => sts.init
    if not is_entail(sts.init, inv):
        correct = False
        logger.error("Initiation check failed")
        model = get_counterexample(z3.And(sts.init, z3.Not(inv)))
        if model:
            logger.error(f"Counterexample: {model}")

    # 2. Check inductiveness: inv && sts.trans => inv'
    if not is_entail(z3.And(sts.trans, inv), inv_in_prime_variables):
        correct = False
        logger.error("Inductiveness check failed")
        model = get_counterexample(z3.And(sts.trans, inv, z3.Not(inv_in_prime_variables)))
        if model:
            logger.error(f"Counterexample: {model}")

    # 3. Check safety/suffciency: inv => sts.post
    # NOTICE: here the guard "C" is Hoare logic is "moved" to te transition relation, and we can just check is_entail(inv, sts.post) for correctness.
    if (not sts.ignore_post_cond) and (not is_entail(inv, sts.post)):
        # for some applications, we may ignore the post condition
        correct = False
        logger.error("Safety check failed")
        model = get_counterexample(z3.And(inv, z3.Not(sts.post)))
        if model:
            logger.error(f"Counterexample: {model}")

    if not correct:
        logger.debug(f"Init: {sts.init}")
        logger.debug(f"Trans: {sts.trans}")
        logger.debug(f"Post: {sts.post}")
        logger.debug(f"Inv: {inv}")
    else:
        logger.info("Invariant verification successful")
    
    return correct

def get_counterexample(formula: z3.ExprRef):
    """Get a counterexample for the given formula"""
    s = z3.Solver()
    s.add(formula)
    if s.check() == z3.sat:
        return s.model()
    return None


