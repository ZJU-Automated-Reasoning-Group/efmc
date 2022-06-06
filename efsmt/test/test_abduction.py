# coding: utf-8
import pytest

from . import TestCase, main
from ..abduction.abduction import abduce
from z3 import *


class TestAbduction(TestCase):

    def test1(self):
        """
        Example:
        pre: existing precondition  Γ: x ≤ 0 ∧ y > 1
        post: target specification  φ: 2x − y + 3z ≤ 10
           Γ ∧ ψ |= φ can be rewritten as ψ |= Γ -> φ.
           So, we use universal qe to compute the sufficient condition of Γ -> φ.
        """
        x, y, z = Ints("x y z")
        pre_cond = And(x <= 0, y > 1)
        post_cond = 2 * x - y + 3 * z <= 10
        assert (abduce(pre_cond, post_cond))

    # def test2(self):
    #    a, b, c = Ints("a b c")
    #    pre = And(b >= c)
    #    post = b > 10
    #    assert abduce(pre, post)


if __name__ == '__main__':
    main()
