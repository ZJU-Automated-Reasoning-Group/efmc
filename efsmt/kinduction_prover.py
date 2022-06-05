# coding: utf-8
# import time
from z3 import *
from typing import List

from .sts import TransitionSystem
from .utils import is_valid


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

    def to_k_induction_system(self):
        """
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

    def k_induction_with_while_guard(self, k: int, pre: z3.ExprRef, post: z3.ExprRef, b: z3.ExprRef, encP: z3.ExprRef):
        """
        E.g., Consider the Hoare-triple below
               {pre} while b do P {post}
               encP encodes P

        FIXME: This function is for testing (we should try to adapt the approach to the next function ....
        """

        # 1.1 base case (k = 1)
        #
        # pre => post
        if not is_valid(Implies(pre, post)):
            if self.debug: print("(pre => post) not valid")
            return "failure"

        # 1.2 base cases (k > 1)
        #
        #            itper
        #         ----   ---                       stop       postper
        #         |        |                         |         |
        # (pre /\ b /\ encP /\ ... /\ b /\ encP /\ not(b)) => post
        #         |                           |
        #         -------------  --------------
        #                      it
        #
        # itper = b /\ encP, 0, 1, ..., k - 2
        itper = And(b, encP)

        # it = /\ itper = /\ (b /\ encP), 0 ... k - 2
        it = And(True)

        stop = Not(b)
        postper = post

        for i in range(k - 1):
            # update it
            it = And(it, itper)

            # update stop
            stop = z3.substitute(stop, *self.var_map[i])

            # update postper
            postper = z3.substitute(postper, *self.var_map[i])

            if not is_valid(Implies(And(pre, it, stop), postper)):
                if self.debug: print("in base cases step", i)
                return "failure"

            # update itper
            # rename i + 1 to i + 2
            itper = z3.substitute(itper, *self.var_map[i + 1])
            # rename i     to i + 1
            itper = z3.substitute(itper, *self.var_map[i])

        # 2. induction step (k > 0)
        #
        #          itper
        #     -----    ----------    stop       postper
        #     |                 |      |           |
        # [ /\(post /\ b /\ encP) /\ not(b) ] => post
        #  |                    |
        #  ----------  ----------
        #            it

        # reuse the stop and update
        stop = z3.substitute(stop, *self.var_map[k - 1])

        # reuse the postper and update
        postper = z3.substitute(postper, *self.var_map[k - 1])

        # redefine itper = post /\ b /\ encP, 0, 1, ... k - 1
        itper = And(post, b, encP)

        # redefine it = /\ itper = /\(post /\ b /\ encP) , 0 ... k - 1
        it = And(True, itper)

        # calculate it
        for i in range(k - 1):
            # update itper
            itper = substitute(itper, *self.var_map[i + 1])
            itper = substitute(itper, *self.var_map[i])
            it = And(it, itper)

        if self.debug: print(it)

        if not is_valid(Implies(And(it, stop), postper)):
            if self.debug: print("in induction step")
            return "failure"

        # no failure return, then return success
        return "success"

    def k_induction(self, k: int, pre: z3.ExprRef, trans: z3.ExprRef, post: z3.ExprRef):
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
        # 1.1 base case (k = 1)
        #
        # pre => post
        if not is_valid(Implies(pre, post)):
            if self.debug: print("(pre => post) not valid")
            return "failure"

        # 1.2 base cases (k > 1)
        #
        #            itper
        #         ----   ---                       stop       postper
        #         |        |                         |         |
        # (pre /\ b /\ encP /\ ... /\ b /\ encP /\ not(b)) => post
        #         |                           |
        #         -------------  --------------
        #                      it
        #
        # itper = b /\ encP, 0, 1, ..., k - 2
        itper = And(b, encP)

        # it = /\ itper = /\ (b /\ encP), 0 ... k - 2
        it = And(True)

        stop = Not(b)
        postper = post

        for i in range(k - 1):
            # update it
            it = And(it, itper)

            # update stop
            stop = z3.substitute(stop, *self.var_map[i])

            # update postper
            postper = z3.substitute(postper, *self.var_map[i])

            if not is_valid(Implies(And(pre, it, stop), postper)):
                if self.debug: print("in base cases step", i)
                return "failure"

            # update itper
            # rename i + 1 to i + 2
            itper = z3.substitute(itper, *self.var_map[i + 1])
            # rename i     to i + 1
            itper = z3.substitute(itper, *self.var_map[i])

        # 2. induction step (k > 0)
        #
        #          itper
        #     -----    ----------    stop       postper
        #     |                 |      |           |
        # [ /\(post /\ b /\ encP) /\ not(b) ] => post
        #  |                    |
        #  ----------  ----------
        #            it

        # reuse the stop and update
        stop = z3.substitute(stop, *self.var_map[k - 1])

        # reuse the postper and update
        postper = z3.substitute(postper, *self.var_map[k - 1])

        # redefine itper = post /\ b /\ encP, 0, 1, ... k - 1
        itper = And(post, b, encP)

        # redefine it = /\ itper = /\(post /\ b /\ encP) , 0 ... k - 1
        it = And(True, itper)

        # calculate it
        for i in range(k - 1):
            # update itper
            itper = substitute(itper, *self.var_map[i + 1])
            itper = substitute(itper, *self.var_map[i])
            it = And(it, itper)

        if self.debug: print(it)

        if not is_valid(Implies(And(it, stop), postper)):
            if self.debug: print("in induction step")
            return "failure"

        # no failure return, then return success
        return "success"

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
def next_var(v):
    if z3.is_real(v):
        return z3.Real("next(%s)" % str(v))
    elif z3.is_int(v):
        return z3.Int("next(%s)" % str(v))
    elif z3.is_bool(v):
        return z3.Bool("next(%s)" % str(v))
    elif z3.is_bv(v):
        return z3.BitVec("next(%s)" % str(v), v.sort().size())
    else:
        raise NotImplementedError


def at_time(v, t):
    # return Symbol("%s@%d" % (v.symbol_name(), t), v.symbol_type())

    if z3.is_real(v):
        return z3.Real("%s@%d" % (str(v), t))
    elif z3.is_int(v):
        return z3.Int("%s@%d" % (str(v), t))
    elif z3.is_bool(v):
        return z3.Bool("%s@%d" % (str(v), t))
    elif z3.is_bv(v):
        return z3.BitVec("%s@%d" % (str(v), t), v.sort().size())
    else:
        raise NotImplementedError
"""
