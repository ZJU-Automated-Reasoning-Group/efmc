# coding: utf-8
"""
NOTE: this one is not used
"""
import logging

import z3


logger = logging.getLogger(__name__)


def is_sat(phi: z3.ExprRef) -> bool:
    s = z3.Solver()
    s.add(phi)
    return s.check() == z3.sat


def is_unsat(phi: z3.ExprRef) -> bool:
    s = z3.Solver()
    s.add(phi)
    return s.check() == z3.unsat


def next_var(variable: z3.ExprRef) -> z3.ExprRef:
    """Returns the 'next' of the given variable"""
    # return z3.Real("next(%s)" % str(v))
    return z3.Real("next(%s)" % str(variable))


def at_time(variable, t):
    """Builds an SMT variable representing v at time t"""
    return z3.Real("%s@%d" % (str(variable), t))


class SimpleTransitionSystem(object):
    """Trivial representation of a Transition System."""

    def __init__(self, variables, init, trans):
        self.variables = variables
        self.init = init
        self.trans = trans


class BMCInduction(object):
    """
    This one is non-incremental
    """

    def __init__(self, system):
        self.system = system

    def get_subs(self, i):
        """Builds a map from x to x@i and from x' to x@(i+1), for all x in system."""
        # TODO: use some cache
        subs_i = []
        for variable in self.system.variables:
            subs_i.append((variable, at_time(variable, i)))
            subs_i.append((next_var(variable), at_time(variable, i + 1)))
        return subs_i

    def get_unrolling(self, k):
        """Unrolling of the transition relation from 0 to k:
        E.g. T(0,1) & T(1,2) & ... & T(k-1,k)
        """
        res = []
        for i in range(k + 1):
            subs_i = self.get_subs(i)
            res.append(z3.substitute(self.system.trans, subs_i))
        return z3.And(res)

    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
           each time encodes a different state
           TODO:
        """
        res = []
        for i in range(k + 1):
            subs_i = self.get_subs(i)
            for j in range(i + 1, k + 1):
                state = []
                subs_j = self.get_subs(j)
                for variable in self.system.variables:
                    v_i = z3.substitute(variable, subs_i)
                    v_j = z3.substitute(variable, subs_j)
                    state.append(v_i != v_j)
                res.append(z3.Or(state))
        return z3.And(res)

    def get_k_hypothesis(self, prop, k):
        """Hypothesis for k-induction: each state up to k-1 fulfills the property"""
        res = []
        for i in range(k):
            subs_i = self.get_subs(i)
            res.append(z3.substitute(prop, subs_i))
        return z3.And(res)  # need to And all?

    def get_bmc(self, prop, k):
        """Returns the BMC encoding at step k"""
        init_0 = z3.substitute(self.system.init, self.get_subs(0))
        prop_k = z3.substitute(prop, self.get_subs(k))
        return z3.And(self.get_unrolling(k), init_0, z3.Not(prop_k))

    def get_k_induction(self, prop, k):
        """Returns the K-Induction encoding at step K"""
        # FIXME
        subs_k = self.get_subs(k)
        prop_k = z3.substitute(prop, subs_k)
        return z3.And(self.get_unrolling(k),
                      self.get_k_hypothesis(prop, k),
                      self.get_simple_path(k),
                      z3.Not(prop_k))

    def check_property(self, prop):
        """Interleaves BMC and K-Ind to verify the property."""
        # FIXME
        print("Checking property %s..." % prop)
        for b in range(20):
            f = self.get_bmc(prop, b)
            print("   [BMC]    Checking bound %d..." % (b + 1))
            if is_sat(f):
                print("--> Bug found at step %d" % (b + 1))
                print(f)
                return

            f = self.get_k_induction(prop, b)
            print("   [K-IND]  Checking bound %d..." % (b + 1))
            if is_unsat(f):
                print("--> The system is safe!")
                return


def main():
    """
    """
    x, y = z3.Reals('x y')
    next_x = next_var(x)
    next_y = next_var(y)
    init = z3.And(x == 0, y == 8)
    trans = z3.Or(z3.And(x < 8, y <= 8, next_x == x + 2, next_y == y - 2),
                  z3.And(x == 8, next_x == 0, y == 0, next_y == 8))
    variables = [x, y]
    sts = SimpleTransitionSystem(variables, init, trans)
    bmcind = BMCInduction(sts)

    true_prop = z3.Not(z3.And(x == 0, y == 0))  # Is valid.
    bmcind.check_property(true_prop)


if __name__ == "__main__":
    main()
