# coding: utf-8
from z3 import *

from . import TestCase, main
from ..sts import TransitionSystem
from ..ef_prover import EFProver


class TestEFSMT(TestCase):

    def test_efsmt(self):
        """
        Specify transition system using Z3's python API (a "naive" trick)
        """
        return

        x, y, px, py = Reals('x y x! y!')

        vars = [x, y, px, py]
        init = And(x == 0, y == 8)
        trans = Or(And(x < 8, y <= 8, px == x + 2, py == y - 2), And(x == 8, px == 0, y == 0, py == 8))
        post = Not(And(x == 0, y == 0))  # Is valid.
        sts = TransitionSystem()
        sts.from_z3_cnts([vars, init, trans, post])

        # Supported conjunctive domains: interval, zone, (bounded) polyhedrons, etc.
        ef_prover = EFProver(sts)  # use template and exists-forall solving
        ef_prover.set_template("poly")
        success = ef_prover.solve_with_z3()
        assert success

    def test_efsmt2(self):
        # Specify transition system using Z3's python API (a "naive" trick)

        x1, c1, t, c2, x2, k1, k2, px1, pc1, pt, pc2, px2, pk1, pk2 = Reals(
            'x1 c1 t c2 x2 k1 k2 x1! c1! t! c2! x2! k1! k2!')
        vars = [x1, c1, t, c2, x2, k1, k2, px1, pc1, pt, pc2, px2, pk1, pk2]
        init = BoolVal(True)
        trans = Or(And(x1 <= 4, pc1 == c1 + t, pc2 == c2 + t, px1 == x1 + t, px2 == x2, pk1 == k1, pk2 == k2),
                   And(x1 > 4, pc1 == pc1, pc2 == pc2, px1 == x1, px2 == x2, pk1 == k1, pk2 == k2))
        post = BoolVal(True)
        sts = TransitionSystem()
        sts.from_z3_cnts([vars, init, trans, post])

        # Supported conjunctive domains: interval, zone, (bounded) polyhedrons, etc.
        ef_prover = EFProver(sts)  # use template and exists-forall solving
        ef_prover.set_template("poly")
        success = ef_prover.solve_with_z3()
        assert success


if __name__ == '__main__':
    main()
