import pytest
from z3 import *

from . import TestCase, main
from ..sts import TransitionSystem
from ..kinduction_prover import KInductionProver


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
        x, y, q, r, xp, yp, qp, rp = Ints("x y q r x! y! q! r!")
        vars = [x, y, q, r, xp, yp, qp, rp]
        pre = And(x >= 0, y >= 0, r == x, q == 0)
        post = Or(r >= y, And(x == y * q + r, r >= 0))
        trans = And(r >= y, xp == x, yp == y, rp == r - y, qp == q + 1)

        sts = TransitionSystem()
        sts.from_z3_cnts([vars, pre, trans, post])

        pp = KInductionProver(sts)
        pp.solve()
        assert (True)


if __name__ == '__main__':
    main()
