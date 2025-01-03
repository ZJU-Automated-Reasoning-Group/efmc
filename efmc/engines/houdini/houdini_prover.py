"""
Houdini algorithm for invariant inference

This module implements the Houdini algorithm for finding maximal inductive invariants,
based on the paper by Flanagan and Leino: "Houdini, an Annotation Assistant for ESC/Java".

Modified from https://github.com/sosy-lab/java-smt/blob/d05b4c8eeb3424be20cc1d9553eaffae81898857/src/org/sosy_lab/java_smt/example/HoudiniApp.java
"""
import z3
from efmc.utils.z3_expr_utils import get_variables


def get_selector_var(idx: int):
    """Create a temp symbol using the given index"""
    return z3.Bool("SEL_{}".format(idx))


def prime(exp: z3.ExprRef):
    """
    traverse the formula and replace all symbols in the formula with their primed version
    :param exp:
    :return: a new formula
    """
    variables = get_variables(exp)
    substitutions = []
    for v in variables:
        sort = v.sort()
        if z3.is_bv_sort(sort):
            substitutions.append((v, z3.BitVec(f"{v}_p", sort.size())))
        elif sort == z3.RealSort():
            substitutions.append((v, z3.Real(f"{v}_p")))
        else:  # default to Int
            substitutions.append((v, z3.Int(f"{v}_p")))
    return z3.substitute(exp, substitutions)


def houdini(lemmas: [z3.ExprRef], transition: z3.ExprRef):
    """Find the maximal inductive subset for the given lemmas and transition.

    This implementation of the Houdini algorithm finds the largest subset of candidate invariants that form an inductive invariant together. It iteratively removes lemmas that break inductiveness until reaching a fixed point.

    Args:
        lemmas (List[z3.ExprRef]): List of candidate invariant expressions to check
        transition (z3.ExprRef): Transition relation of the system

    Returns:
        dict: Dictionary mapping indices to lemmas that form the maximal inductive subset

    Example:
        >>> lemmas = [x >= 0, x <= 10]  # candidate invariants
        >>> trans = And(x' == x + 1)    # transition relation
        >>> inductive = houdini(lemmas, trans)
    """
    annotated = []
    annotated_primes = []
    indexed = {}
    for i in range(len(lemmas)):
        lemma = lemmas[i]
        primed = prime(lemma)
        annotated.append(z3.Or(lemma, get_selector_var(i)))
        annotated_primes.append(z3.Or(primed, get_selector_var(i)))
        indexed[i] = lemma

    prover = z3.Solver()
    prover.add(transition)
    prover.add(z3.And(annotated))
    prover.add(z3.Not(z3.And(annotated_primes)))

    while prover.check() != z3.unsat:
        m = prover.model()
        for i in range(len(annotated_primes)):
            annotated_prime = annotated_primes[i]
            # find a counter-example of being inductive?
            if z3.is_false(m.eval(annotated_prime)):
                prover.add(get_selector_var(i))
                del indexed[i]
    return indexed


def demo_houdini():
    """
    Guess-and-check
     - ML: SVM, DNN, Decision tree,..
     - Grammar:
    """
    # Test
    x = z3.Int("X")
    x_primed = z3.Int("X_p")
    # for the transition X'=X+1 the lemma X>1 and X>2 are valid, but X<1 is invalid.
    lemmas = [x > 1, x > 2, x < 1]
    transition = x_primed == x + 1
    # use Houdini to compute the maximal inductive subset
    result = houdini(lemmas, transition)
    print(result)


demo_houdini()
