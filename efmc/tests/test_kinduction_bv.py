# coding: utf-8
import time
import z3

from efmc.tests import TestCase, main
from efmc.sts import TransitionSystem
from efmc.engines.kinduction.kinduction_prover import KInductionProver


class TestKInductionBV(TestCase):

    def test_kind_bv(self):
        print("Running one test...")

        x, y, px, py = z3.BitVecs('x y x! y!', 8)
        all_vars = [x, y, px, py]
        init = z3.And(x == 0, y == 0)
        trans = z3.And(z3.And(z3.ULT(x, 8), z3.ULT(y, 8)),
                       px == x + 1, py == y + 1)
        post = z3.Implies(z3.UGE(y, 8), z3.And(x == 8, y == 8))
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        sts.set_signedness("unsigned")
        pp = KInductionProver(sts)
        pp.use_aux_invariant = True
        start = time.time()
        pp.solve(k=20)
        print("time: ", time.time() - start)
        assert True


if __name__ == '__main__':
    main()