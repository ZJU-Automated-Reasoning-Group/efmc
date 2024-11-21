"""
Houdini algorithm for invariant inference

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
    all_vars = get_variables(exp)
    rep_map = []
    for v in all_vars:
        rep_map.append((v, z3.Int("{}_p".format(str(v)))))
    return z3.substitute(exp, rep_map)


def houdini(lemmas: [z3.ExprRef], transition: z3.ExprRef):
    """Find the maximal inductive subset for the given lemmas and transition"""
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


def test_houdini():
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


test_houdini()
