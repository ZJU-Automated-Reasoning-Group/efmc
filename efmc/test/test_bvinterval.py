# coding: utf-8
import z3

from . import TestCase, main
from ..ef_prover import EFProver
from ..sts import TransitionSystem


class TestBitVecIntervalTemplate(TestCase):

    def test_bv_interval(self):
        """
        Specify transition system using Z3's python API (a "naive" trick)
        """
        x, y, px, py = z3.BitVecs('x y x! y!', 16)
        all_vars = [x, px]
        init = x == 0
        trans = z3.And(z3.ULT(x, 8), px == x + 1)
        post = z3.Implies(z3.UGE(x, 8), x == 8)
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])

        # Supported conjunctive domains: interval, zone, (bounded) polyhedrons, etc.
        ef_prover = EFProver(sts)  # use template and exists-forall solving
        ef_prover.set_template("power_bv_interval")
        vc = ef_prover.generate_vc()
        print(vc)
        # ef_prover.solve()
        # print(sts.to_chc_str())


if __name__ == '__main__':
    main()
