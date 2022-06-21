# coding: utf-8
import z3

from . import TestCase, main
from ..sts import TransitionSystem
from ..predabs import PredicateAbstractionProver


class TestPredicateAbstraction(TestCase):

    def test_bool_program(self):
        x, y, xp, yp = z3.Bools("x y x! y!")
        init = z3.And(x, y)
        trans = z3.And(z3.Implies(y, xp == y, yp == y),
                       z3.Implies(z3.Not(y), xp == z3.Not(y), yp == y))
        post = x
        preds = [x, y]

        vars = [x, y, xp, yp]
        sts = TransitionSystem()
        sts.from_z3_cnts([vars, init, trans, post])

        pp = PredicateAbstractionProver(sts)
        pp.set_predicates(preds)
        pp.solve()


if __name__ == '__main__':
    main()
