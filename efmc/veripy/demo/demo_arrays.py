import efmc.veripy as vp
from efmc.veripy import verify, invariant
from typing import List

vp.enable_verification()
vp.scope('arrays')

@verify(
    requires=[],
    ensures=['xs[0] == v']
)
def set_first(xs: List[int], v: int) -> None:
    xs[0] = v


@verify(
    requires=['n >= 0'],
    ensures=[]
)
def array_argmax(a: List[int], n: int) -> int:
    i = 0
    j = 0
    while j < n:
        invariant('0 <= j and j <= n')
        invariant('0 <= i and i <= j')
        j = j + 1
    return i


vp.verify_all()


