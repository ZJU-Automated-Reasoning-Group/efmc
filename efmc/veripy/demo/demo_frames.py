import efmc.veripy as vp
from efmc.veripy import verify, invariant
from typing import List

vp.enable_verification()
vp.scope('frames')

# Simple counter with modifies and old
@verify(requires=['n >= 0'], ensures=['ans == old(n)'], modifies=['ans'])
def returns_old_of_n(n: int) -> int:
    ans = n
    return ans

# Reads vs modifies demo
@verify(requires=['len(xs) > 0'], ensures=['xs[0] == old(xs[0]) + 1'], modifies=['xs'])
def inc_first(xs: List[int]) -> None:
    xs[0] = xs[0] + 1

vp.verify_all()


