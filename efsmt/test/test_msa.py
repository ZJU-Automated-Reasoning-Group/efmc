# coding: utf-8
import pytest
import sys
from z3 import *

from . import TestCase, main
from .formula_generator import FormulaGenerator
from ..abduction.mistral_z3 import MSASolver
from ..utils import get_variables, is_sat


def find_model(fml):
    msa_finder = MSASolver()
    msa_finder.init_from_formula(fml)
    print("All variables: ", get_variables(fml))
    m = msa_finder.find_small_model()
    print("Minimal mdoel: \n", m)
    if msa_finder.validate_small_model(m):
        print("validation success!")
    return True


def test_msa():
    try:
        w, x, y, z = BitVecs("w x y z", 8)
        fg = FormulaGenerator([x, y, z])
        fml = fg.generate_formula()
        if is_sat(fml):
            return find_model(fml)
        return False
    except Exception as ex:
        print(ex)
        return False


class TestMSA(TestCase):
    for _ in range(5):
        test_res = test_msa()
        if test_res:
            break

    assert True


if __name__ == '__main__':
    main()
