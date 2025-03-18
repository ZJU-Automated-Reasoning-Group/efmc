"""
Verifying Boolean Programs using "Predicate abstraction"

 Given a set of Boolean variables P and a transition system S,
 it finds the strongest inductive invariant expressible as the Boolean combination of P.
"""
from typing import List, Optional       

import z3

from efmc.utils import negate, is_valid, ctx_simplify, eval_predicates
from efmc.sts import TransitionSystem


def strongest_consequence(fml: z3.ExprRef, predicates: List[z3.ExprRef], k=None):
    """
    Compute the strongest necessary condition of fml that is the Boolean combination of preds
    Following CAV'06 paper "SMT Techniques for Fast Predicate Abstraction"
    """
    s = z3.Solver()
    s.add(fml)
    res = []
    while s.check() == z3.sat:
        m = s.model()
        # each proj is a sufficient (or necessary?) condition that
        # "generalizes" from the current model????
        # TODO: use prime implicate (i.e., throwing away some p in preds)
        proj = z3.And(eval_predicates(m, predicates))
        res.append(proj)
        # block the current one
        s.add(negate(proj))

    return z3.simplify(z3.Or(res))


def weakest_sufficient_condition(fml: z3.ExprRef, predicates: List[z3.ExprRef]):
    notfml = z3.Not(fml)
    sc = strongest_consequence(notfml, predicates)
    return z3.simplify(z3.Not(sc))


def fixpoint(old_inv: z3.ExprRef, inv: z3.ExprRef) -> bool:
    return is_valid(z3.Implies(inv, old_inv))


class PredicateAbstractionProver:
    def __init__(self, system: TransitionSystem):
        self.sts = system
        self.preds = []
        """
        var_map = [(x, xp), (y, yp)]
        var_map_rev = [(xp ,x), (yp, y)]
        """
        self.var_map = []
        self.var_map_rev = []
        for i in range(len(self.sts.variables)):
            self.var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            self.var_map_rev.append((self.sts.prime_variables[i], self.sts.variables[i]))

    def set_predicates(self, predicates):
        """The element in the domain is the Boolean combinations of a set of predicates"""
        self.preds = predicates

    def solve(self, timeout: Optional[int] = None):
        preds_prime = []
        for pred in self.preds:
            preds_prime.append(z3.substitute(pred, self.var_map))

        old_inv = False
        inv = self.sts.init
        i = 0
        while not fixpoint(old_inv, inv):
            print("\nInv at ", i, ": ", inv)
            i = i + 1
            # onestep = stronget_consequence_simple(And(inv, trans), preds_prime) # another imple
            onestep = strongest_consequence(z3.And(inv, self.sts.trans), preds_prime)
            onestep = z3.substitute(onestep, self.var_map_rev)
            old_inv = inv  # Is this correct?
            inv = z3.simplify(z3.Or(inv, onestep))
        # print("\n")

        if is_valid(z3.Implies(inv, self.sts.post)):
            print(ctx_simplify(inv))
            print(">>> SAFE\n\n")
        else:
            print(">>> MAYBE?!?!\n\n")

        return


def run_test_case(name, init_formula, trans_formula, post_formula, predicates):
    """Helper function to run a test case with the given parameters"""
    print(f"\n=== Running test case: {name} ===")
    sts = TransitionSystem()
    sts.from_z3_cnts([predicates + [p_var for p, p_var in var_map],
                      init_formula, trans_formula, post_formula])

    pp = PredicateAbstractionProver(sts)
    pp.set_predicates(predicates)
    pp.solve()


if __name__ == '__main__':
    # Original test case
    print("=== Original test case ===")
    x, y, xp, yp = z3.Bools("x y x! y!")
    init = z3.And(x, y)
    trans = z3.And(z3.Implies(y, z3.And(xp == y, yp == y)),
                   z3.Implies(z3.Not(y), z3.And(xp == z3.Not(y), yp == y)))
    post = x
    preds = [x, y]

    all_vars = [x, y, xp, yp]
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])

    pp = PredicateAbstractionProver(sts)
    pp.set_predicates(preds)
    pp.solve()

    # Additional test cases

    # Test case 1: Simple counter
    a, b, c, ap, bp, cp = z3.Bools("a b c a! b! c!")
    var_map = [(a, ap), (b, bp), (c, cp)]

    # Counter that increments from 000 to 111 in binary
    init_1 = z3.And(z3.Not(a), z3.Not(b), z3.Not(c))
    trans_1 = z3.And(
        ap == z3.Xor(a, z3.And(b, c)),
        bp == z3.Xor(b, c),
        cp == z3.Not(c)
    )
    post_1 = z3.Implies(z3.And(a, b, c), z3.And(a, b, c))  # Trivially true

    run_test_case("Binary Counter", init_1, trans_1, post_1, [a, b, c])

    # Test case 2: Mutual exclusion
    p, q, p_crit, q_crit, pp, qp, p_critp, q_critp = z3.Bools("p q p_crit q_crit p! q! p_crit! q_crit!")
    var_map = [(p, pp), (q, qp), (p_crit, p_critp), (q_crit, q_critp)]

    # Simple mutual exclusion protocol
    init_2 = z3.And(z3.Not(p_crit), z3.Not(q_crit), z3.Not(p), z3.Not(q))

    # Transition relation for a simple mutex protocol
    trans_2 = z3.And(
        # Process p
        z3.Implies(z3.And(z3.Not(p), z3.Not(p_crit)), z3.And(pp == True, p_critp == z3.Not(q_crit))),
        z3.Implies(z3.And(p, z3.Not(p_crit)), z3.And(pp == False, p_critp == True)),
        z3.Implies(p_crit, z3.And(pp == False, p_critp == False)),

        # Process q
        z3.Implies(z3.And(z3.Not(q), z3.Not(q_crit)), z3.And(qp == True, q_critp == z3.Not(p_crit))),
        z3.Implies(z3.And(q, z3.Not(q_crit)), z3.And(qp == False, q_critp == True)),
        z3.Implies(q_crit, z3.And(qp == False, q_critp == False))
    )

    # Mutual exclusion property
    post_2 = z3.Not(z3.And(p_crit, q_crit))

    run_test_case("Mutual Exclusion", init_2, trans_2, post_2, [p, q, p_crit, q_crit])

    # Test case 3: Simple Fibonacci-like sequence property
    i, j, ip, jp = z3.Bools("i j i! j!")
    var_map = [(i, ip), (j, jp)]

    # Initialize i and j to false
    init_3 = z3.And(z3.Not(i), z3.Not(j))

    # Transition: i' = j, j' = i XOR j
    trans_3 = z3.And(
        ip == j,
        jp == z3.Xor(i, j)
    )

    # Property: i and j are never both true simultaneously
    post_3 = z3.Not(z3.And(i, j))

    run_test_case("Fibonacci-like Sequence", init_3, trans_3, post_3, [i, j])
