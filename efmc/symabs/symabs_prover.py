# coding: utf-8
import time
import logging

import z3

from . import NumericalAbstraction
from ..sts import TransitionSystem
from ..utils import is_valid, is_entail, ctx_simplify

"""
Using Symbolic Abstraction to find invariants
 + Symbolic abstraction + iteration
"""

logger = logging.getLogger(__name__)


def fixpoint(old_inv: z3.ExprRef, inv: z3.ExprRef) -> bool:
    # TODO: Is this correct?
    # TODO: do not need a solver to decide inductive
    return is_valid(z3.Implies(inv, old_inv))


def fixpoint_with_trans(inv: z3.ExprRef, trans: z3.ExprRef, inv_in_prime: z3.ExprRef) -> bool:
    # TODO: is this correct or the previous one???
    return is_valid(z3.Implies(z3.And(inv, trans), inv_in_prime))


class SymbolicAbstractionProver:
    def __init__(self, system: TransitionSystem):
        self.sts = system
        """
        var_map = [(x, xp), (y, yp)]
        var_map_rev = [(xp ,x), (yp, y)]
        """
        self.var_map = []
        self.var_map_rev = []
        for i in range(len(self.sts.variables)):
            self.var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            self.var_map_rev.append((self.sts.prime_variables[i], self.sts.variables[i]))

    def check_invariant(self, inv: z3.BoolRef):
        """
        Check whether the generated invariant is correct (and good)
        """
        correct = True
        # 1. Init
        if not is_entail(self.sts.init, inv):
            correct = False
            print("Init wrong!")

        # 2. Inductive
        # FIXME: the termination criteria fixpoint(old_inv, inv) seems to be different from the one below??
        # TODO: should we use fixpoint(old_inv, inv) or fixpoint_with_tarns(old_inv, trans, inv)??
        # """
        inv_in_prime = z3.substitute(inv, self.var_map)
        if not is_entail(z3.And(self.sts.trans, inv), inv_in_prime):
            correct = False
            print("Not inductive!")
            print("Inv: ", z3.simplify(inv))
            print("Inv Pri: ", z3.simplify(inv_in_prime))
            print(self.sts)
            # exit(0)
        # """
        # 3. Post

        if not is_entail(inv, self.sts.post):
            correct = False
            print("Post not verified!")
            print("Inv: ", ctx_simplify(inv))
            print(self.sts)
        else:
            print("Post verified")
            # print(self.sts)

        return correct

    def apply_join(self, inv):
        """
        TODO: join is not enough, it seems we need widening to stop
        """
        sym_abs = NumericalAbstraction()
        sym_abs.init_from_fml(inv, self.sts.variables)
        return sym_abs.interval_abs()

    def solve(self) -> None:
        print("SymAbs starting!!!")
        start = time.time()
        old_inv = z3.BoolVal(False)
        # TODO: init could be complex (so, we need to convert it into intervals first?)
        inv = self.sts.init
        i = 0
        # """
        while not fixpoint(old_inv, inv):
            print("\nInv at ", i, ": ", inv)
            i = i + 1
            sym_abs = NumericalAbstraction()
            # TODO: is And(inv, self.sts.trans) correct? (it may violate the "unrolling order")
            sym_abs.init_from_fml(z3.And(inv, self.sts.trans), self.sts.prime_variables)
            onestep = sym_abs.interval_abs()
            # FIXME: Some versions of Z3's Optimize() has bugs
            # FIXME: Maybe we should be able to choose  self-compiled/pre-built python packages for Z3
            # FIXME: but not the one ....
            print("onestep: ", onestep)
            s = z3.Solver()
            s.add(z3.Not(z3.Implies(z3.And(inv, self.sts.trans), onestep)))
            if s.check() == z3.sat:
                print("interval not entailed by???")
                print(z3.And(inv, self.sts.trans))
                print(onestep)
                # exit(0)

            onestep = z3.substitute(onestep, self.var_map_rev)
            # print("onestep: ", onestep)
            old_inv = inv
            inv = z3.simplify(z3.Or(inv, onestep))
            # inv = self.apply_join(Or(inv, onestep)) #???

        # print("INV:", inv)
        duration = time.time() - start

        if self.check_invariant(inv):
            print("Sym Abs success time: ", duration)
            print("Invariant: ", ctx_simplify(inv))
        else:
            print("Sym Abs fail time: ", duration)
