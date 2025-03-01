"""Test the Houdini prover"""

import z3
from efmc.engines.houdini.houdini_prover import HoudiniProver
from efmc.sts import TransitionSystem
from efmc.tests.simple_sts import get_int_sys1, get_int_sys2, get_int_sys3, get_int_sys4, get_int_sys5


def test_houdini():
    # define a simple transition system
    sts = TransitionSystem()
    sts.from_z3_cnts(list(get_int_sys1()))
    prover = HoudiniProver(sts)
    result = prover.solve()
    print(result)


def test_houdini_2():
    sts = TransitionSystem()
    sts.from_z3_cnts(list(get_int_sys2()))
    prover = HoudiniProver(sts)
    result = prover.solve()
    print(result)


def test_houdini_3():
    sts = TransitionSystem()
    sts.from_z3_cnts(list(get_int_sys3()))
    prover = HoudiniProver(sts)
    result = prover.solve()
    print(result)   


def test_houdini_4():
    sts = TransitionSystem()
    sts.from_z3_cnts(list(get_int_sys4()))
    prover = HoudiniProver(sts)
    result = prover.solve()
    print(result)
    

if __name__ == "__main__":
    test_houdini()
