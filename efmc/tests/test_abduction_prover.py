# coding: utf-8
import time
import z3

from efmc.tests import TestCase, main
from efmc.sts import TransitionSystem
from efmc.engines.abduction.abduction_prover import AbductionProver
from efmc.engines.kinduction.kind_prover import KInductionProver
from efmc.engines.pdr.pdr_prover import PDRProver
from efmc.tests.simple_sts import get_int_sys1, get_int_sys5


class TestAbductionProver(TestCase):


    def test_abd2(self):
        print("Running one test...")
        sts = TransitionSystem()
        sts.from_z3_cnts(get_int_sys1())

        # k-induction
        kind_prover = KInductionProver(sts)
        kind_prover.use_aux_invariant = False
        res = kind_prover.solve(k=20)
        print('kind prover res: ', res)
        print("======================================")

        # PDR
        pdr_prover = PDRProver(sts)
        res = pdr_prover.solve()
        print('PDR prover res: ', res)
        print("======================================")

        abd_prover = AbductionProver(sts)
        res = abd_prover.solve()
        print("abd prover res: ", res)
        print("======================================")
        # print("time: ", time.time() - start)


if __name__ == '__main__':
    main()
