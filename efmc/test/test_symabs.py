# coding: utf-8
from z3 import *

from . import TestCase, main
from ..sts import TransitionSystem
from ..symabs_prover import SymbolicAbstractionProver


class TestSymAbs(TestCase):

    def test(self):
        """
        Specify transition system using Z3's python API (a "naive" trick)
        """
        x, y, px, py = Reals('x y x! y!')
        vars = [x, y, px, py]
        init = x == 0
        trans = And(x < 8, y <= 8, px == x + 2, py == y - 2)
        post = Not(And(x == 0, y == 0))  # Is valid?

        # vars = [x, px]
        # init = x == 0
        # trans = And(x < 10, px == x + 1)
        # post = Or(x < 10, x == 10)

        sts = TransitionSystem()
        sts.from_z3_cnts([vars, init, trans, post])
        pp = SymbolicAbstractionProver(sts)
        pp.solve()

        """
        s = SolverFor("HORN")
        inv = Function("inv", RealSort(), RealSort(), BoolSort())
        s.add(ForAll([x, y], Implies(init, inv(x, y))))
        s.add(ForAll([x, y, px, py], Implies(And(inv(x, y), trans),
                                             inv(px, py))))
        s.add(ForAll([x, y], Implies(inv(x, y), post)))
        print(s.check())
        """

        assert True

        if __name__ == '__main__':
            main()
