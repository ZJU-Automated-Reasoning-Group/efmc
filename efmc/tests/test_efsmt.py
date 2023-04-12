# coding: utf-8
import z3

from efmc.tests import TestCase, main
from efmc.engines.ef.ef_prover import EFProver
from efmc.sts import TransitionSystem


class TestEFSMT(TestCase):

    def test_efsmt(self):
        """
        Specify transition system using Z3's python API (a "naive" trick)
        """
        print("testing efsmt")
        x, y, px, py = z3.Reals('x y x! y!')

        all_vars = [x, y, px, py]
        init = z3.And(x == 0, y == 8)
        trans = z3.Or(z3.And(x < 8, y <= 8, px == x + 2, py == y - 2), z3.And(x == 8, px == 0, y == 0, py == 8))
        post = z3.Not(z3.And(x == 0, y == 0))  # Is valid.
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])

        # Supported conjunctive domains: interval, zone, (bounded) polyhedrons, etc.
        ef_prover = EFProver(sts, validate_invariant=True)
        ef_prover.set_template("power_interval", num_disjunctions=2)
        success = ef_prover.solve()
        assert True

    def test_efsmt2(self):
        # Specify transition system using Z3's python API (a "naive" trick)
        print("testing efsmt2")

        x1, c1, t, c2, x2, k1, k2, px1, pc1, pt, pc2, px2, pk1, pk2 = z3.Reals(
            'x1 c1 t c2 x2 k1 k2 x1! c1! t! c2! x2! k1! k2!')
        all_vars = [x1, c1, t, c2, x2, k1, k2, px1, pc1, pt, pc2, px2, pk1, pk2]
        init = z3.BoolVal(True)
        trans = z3.Or(z3.And(x1 <= 4, pc1 == c1 + t, pc2 == c2 + t, px1 == x1 + t, px2 == x2, pk1 == k1, pk2 == k2),
                      z3.And(x1 > 4, pc1 == pc1, pc2 == pc2, px1 == x1, px2 == x2, pk1 == k1, pk2 == k2))
        post = z3.BoolVal(True)
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])

        # Supported conjunctive domains: interval, zone, (bounded) polyhedrons, etc.
        ef_prover = EFProver(sts, validate_invariant=True)
        ef_prover.set_template("power_interval", num_disjunctions=2)
        ef_prover.set_solver("z3api")  # Use z3's Python API
        # ef_prover.set_solver("cvc5")
        success = ef_prover.solve()
        assert success


if __name__ == '__main__':
    main()
