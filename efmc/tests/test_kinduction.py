# coding: utf-8
import time
import z3

from efmc.tests import TestCase, main
from efmc.sts import TransitionSystem
from efmc.engines.kinduction.kinduction_prover import KInductionProver
from efmc.tests.simple_sts import get_int_sys1, get_int_sys2, get_int_sys3, get_int_sys4, get_int_sys5, get_int_sys6


class TestKInduction(TestCase):

    def test_kind1(self):
        return
        """
        Description:
        It calculates q = x / y and r = x % y.
        {x >= 0, y >= 0, r == x, q == 0}
        while(r >= y)
            r = r - y
            q = q + 1
        {x == y * q + r, r >= 0}
        """
        print("Running one test...")
        x, y, q, r, xp, yp, qp, rp = z3.Ints("x y q r x! y! q! r!")
        all_vars = [x, y, q, r, xp, yp, qp, rp]
        pre = z3.And(x >= 0, y >= 0, r == x, q == 0)
        post = z3.Or(r >= y, z3.And(x == y * q + r, r >= 0))
        trans = z3.And(r >= y, xp == x, yp == y, rp == r - y, qp == q + 1)

        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, pre, trans, post])
        pp = KInductionProver(sts)
        start = time.time()
        pp.solve(k=20)
        print("time: ", time.time() - start)
        assert True

    def test_kind2(self):
        print("Running one test...")
        sts = TransitionSystem()
        sts.from_z3_cnts(get_int_sys3())
        pp = KInductionProver(sts)
        pp.use_aux_invariant = False
        start = time.time()
        pp.solve(k=20)
        print("time: ", time.time() - start)
        assert True


if __name__ == '__main__':
    main()
