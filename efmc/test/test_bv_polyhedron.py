# coding: utf-8
import logging
import z3

from efmc.test import TestCase, main
from efmc.engines.ef.ef_prover import EFProver
from efmc.sts import TransitionSystem


class TestBitVecPolyhedronTemplate(TestCase):

    def test_bv_poly(self):
        """
        Specify transition system using Z3's python API (a "naive" trick)
        """
        logging.basicConfig(level=logging.DEBUG)
        x, y, px, py = z3.BitVecs('x y x! y!', 10)
        all_vars = [x, y, px, py]
        init = z3.And(x == 0, y == 0)
        trans = z3.And(z3.And(z3.ULT(x, 8), z3.ULT(y, 8)),
                             px == x + 1, py == y + 1)
        post = z3.Implies(z3.UGE(x, 8), x == 8)
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])

        # Supported conjunctive domains: interval, zone, (bounded) polyhedrons, etc.
        ef_prover = EFProver(sts)  # use template and exists-forall solving
        ef_prover.set_template("bv_poly")
        ef_prover.solve()


if __name__ == '__main__':
    main()
