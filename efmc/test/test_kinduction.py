# coding: utf-8
import z3

from efmc.test import TestCase, main
from efmc.sts import TransitionSystem
from efmc.engines.kinduction.kinduction_prover import KInductionProver


class TestKInduction(TestCase):

    def test_kind(self):
        """
        Description:
        It calculates q = x / y and r = x % y.
        """
        #
        """
        {x >= 0, y >= 0, r == x, q == 0}
        while(r >= y)
            r = r - y
            q = q + 1
        {x == y * q + r, r >= 0}
        """
        x, y, q, r, xp, yp, qp, rp = z3.Ints("x y q r x! y! q! r!")
        all_vars = [x, y, q, r, xp, yp, qp, rp]
        pre = z3.And(x >= 0, y >= 0, r == x, q == 0)
        post = z3.Or(r >= y, z3.And(x == y * q + r, r >= 0))
        trans = z3.And(r >= y, xp == x, yp == y, rp == r - y, qp == q + 1)

        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, pre, trans, post])

        pp = KInductionProver(sts)
        pp.solve()
        assert True


if __name__ == '__main__':
    main()
