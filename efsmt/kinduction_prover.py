# coding: utf-8
# import time
from z3 import *
from typing import List

from .sts import TransitionSystem
from .utils import is_valid

"""
Based on https://github.com/SRI-CSL/sally/blob/master/src/engine/kind/kind_engine.cpp
"""


class KInductionProver(object):
    """
    k-induction
    """

    def __init__(self, system: TransitionSystem):
        self.sts = system
        self.preds = []

        # mapping
        self.var_map = {}

        self.debug = True

        # [{}, {}]
        self.k_induction_vars = []
        for _ in self.sts.variables:
            self.k_induction_vars.append({})

        self.set_k(3)

    def set_k(self, k: int):
        """
        Assume all variables are predefined when encoding formula,
        We use x[0] instead of x, x[1] instead of x! (or x')
        """
        self.k = k

    def get_input_variabels(self, n):

        return n

    def get_state_variables(self, n):

        return n

    def get_transition_formula(self, n):

        return

    def to_k_induction_system(self):
        """
        #FIXME: this is not a good idea
        Currently, we maintain another group of variables for k-induction
        (This might no be very elegant)

        Assume there are four variables x, y, q, r. And the k is 3

        self.k_induction_vars is
        [{0: x0, 1: x1, 2: x2}, {0: y0, 1: y1, 2: y2}, {0: q0, 1: q1, 2: q2}, {0: r0, 1: r1, 2: r2}]

        self.var_map is
        {0: [(x0, x1), (y0, y1), (q0, q1), (r0, r1)], 1: [(x1, x2), (y1, y2), (q1, q2), (r1, r2)]}
        """
        for i in range(self.k):
            for j in range(len(self.k_induction_vars)):
                self.k_induction_vars[j][i] = z3.Int(str(self.sts.variables[j]) + str(i))

        for i in range(self.k):
            if i > 0:
                self.var_map[i - 1] = [(vvars[i - 1], vvars[i]) for vvars in self.k_induction_vars]

        # print(self.k_induction_vars)
        # print(self.var_map)

        vars_to_kinduction_vars = []
        all_vars_to_kinduction_vars = []
        for i in range(len(self.sts.variables)):
            vars_to_kinduction_vars.append((self.sts.variables[i], self.k_induction_vars[i][0]))
            all_vars_to_kinduction_vars.append((self.sts.variables[i], self.k_induction_vars[i][0]))
            all_vars_to_kinduction_vars.append((self.sts.prime_variables[i], self.k_induction_vars[i][1]))

        # print(vars_to_kinduction_vars)
        # print(all_vars_to_kinduction_vars)

        pre_cond = z3.substitute(self.sts.init, vars_to_kinduction_vars)
        trans_cond = z3.substitute(self.sts.trans, all_vars_to_kinduction_vars)
        post_cond = z3.substitute(self.sts.post, vars_to_kinduction_vars)
        return pre_cond, trans_cond, post_cond

    def k_induction(self, k: int, pre: z3.ExprRef, trans: z3.ExprRef, post: z3.ExprRef):
        """
         We try to find a k such that:
        (1) P holds at steps 0, ..., k-1, i.e.
        I and T_0 and ... and T_{i-1} => P(x_i), for 0 <= i < k
        (2) P holding at k consecutive step, implies it holds in the next one, i.e.
        and_{0 <= i < k} (P_i and T_i) => P_k

        Use two solvers:
        * solver 1 accumulates the antecedent of (1), i.e. I and T_0 and ... and T_{k-1}
        * solver 2 accumulates the antecedent of (2), i.e. P_0 and T_0 and ....P_{k-1} and T_{k-1}

        solver1: check (not P). if sat we found a counterexample.
        solver2: check (not P). if unsat we proved the property.
        """
        # SMT solver for proving (1)
        solver1 = z3.Solver()
        # SMT solver for proving (2)
        solver2 = z3.Solver()

        # Initial states go to solver 1
        solver1.add(pre)  # FIXME: is this correct?

        property_not_k = BoolVal(True)  # FIXME

        # Induction loop
        k = 0
        while True:
            if k >= self.k:
                return "unknown"

            if self.debug: print("K-Induction: checking initialization ", k)
            # Check the current unrolling (1)
            solver1.push()
            solver1.add(property_not_k)
            r1 = solver1.check()
            if self.debug: print("K-Induction: got ", r1)

            # See what happened
            if r1 == z3.sat:
                return "unsafe"
            elif r1 == z3.unsat:
                # No counterexample found, continue
                break
            elif r1 == z3.unknown:
                return "unknown"
            else:
                assert False

            # Pop the solver
            solve1.pop()

            # For (2) add property and transition

            # Unroll the transition relation once more

            # For (2) add property and transition

            # Should we do the check at k
            check_consection = True
            if check_consection:
                if self.debug: print("K-Induction: checking consecution ", k)

            # Unroll the property once more
            k = k + 1

            # Check the current unrolling (2)
            if check_consection:
                solver1.push()
                solver2.add(BoolVal(True))  # FIXME
                r2 = solver2.check()

                if self.debug: print("K-Induction solver2 got ", r2)

                if r2 == z3.unsat:
                    return "proved"
                elif r2 == z3.sat or r2 == z3.unknown:
                    break  # or continue?
                else:
                    assert False

                solver2.pop()

            # One more transition for solver 1
            solver1.add()

    def solve(self):
        can_prove = False
        pre, trans, post = self.to_k_induction_system()

        # print(pre, trans, post)

        for t in range(1, self.k):
            if self.k_induction(t, pre, trans, post) == "success":
                print("can use k-induction to prove, k =", t)
                can_prove = True
                break
        if not can_prove:
            print(" can't use k-induction to prove when k <", self.k)


"""
    E.g., Consider the Hoare-triple below
        {pre} while b do P {post}
    We "fuse" the condition "b" to the trans and post. That is, following
    the SyGuS invariant format, we deal with the following transition system
            - pre = pre
            - trans = And(b, P)
            - post = Implies(Not(b), post)
        Alternatively, post = Or(b, post)

    FIXME: but, since we "remove" b, how should we adapt the algorithm that uses "b"?
    Especially, the "stop" condition
    Can we just regard b as False or True? (but the values of variables in the condition may change...
"""
