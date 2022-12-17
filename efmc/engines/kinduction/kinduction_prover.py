# coding: utf-8
# import time
import logging
import z3
# from typing import List
from efmc.sts import TransitionSystem

"""
#  Checking  safety  properties  using  induction  and  a SAT-solver
#     Sheeran, Singh, Stalmarck @ FMCAD 2000
#
"""

logger = logging.getLogger(__name__)

# TODO: integrate the one in the kinduction dir


class TraceHelper(object):
    """
    Not used now
    """

    def __init__(self, system: TransitionSystem):

        self.sts = system
        # mapping # this name is not good
        self.var_map = {}
        # [{}, {}]
        self.k_induction_vars = []
        for _ in self.sts.variables:
            self.k_induction_vars.append({})

    def to_k_induction_system(self, kind_max):
        """
        #FIXME: Currently, we maintain another group of variables for k-induction \
        and the variables are created eagerly, which might not be very elegant
        (But could be useful in parallel analysis??)

        Assume there are four variables x, y, q, r. And the k is 3

        self.k_induction_vars is
        [{0: x0, 1: x1, 2: x2}, {0: y0, 1: y1, 2: y2}, {0: q0, 1: q1, 2: q2}, {0: r0, 1: r1, 2: r2}]

        self.var_map is
        {0: [(x0, x1), (y0, y1), (q0, q1), (r0, r1)], 1: [(x1, x2), (y1, y2), (q1, q2), (r1, r2)]}
        """
        for i in range(kind_max):
            for j in range(len(self.k_induction_vars)):
                self.k_induction_vars[j][i] = z3.Int(str(self.sts.variables[j]) + str(i))

        for i in range(kind_max):
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

    def get_state_variables(self, k):
        """
        Get the state variables at k.
        self.var_map is {0: [(x0, x1), (y0, y1), (q0, q1), (r0, r1)], 1: [(x1, x2), (y1, y2), (q1, q2), (r1, r2)]}
        """
        return [var_pair[0] for var_pair in self.var_map[k]]

    def get_transition_formula(self, n):
        """
        Given a transition formula, return a transition formula
         from k to k + 1 step.
        """
        return


class KInductionProver(object):
    """
    k-induction
    """

    def __init__(self, system: TransitionSystem):
        self.sts = system

    def solve(self):
        return True
        # raise NotImplementedError

        # print("can use k-induction to prove, k =", t)
