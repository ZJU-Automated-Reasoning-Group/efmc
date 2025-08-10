import efmc.veripy as vp
from efmc.veripy import verify, invariant

vp.enable_verification()
vp.scope('calls')


@verify(requires=['n >= 0'], ensures=['ans == n + 1'])
def inc(n: int) -> int:
    return n + 1


@verify(requires=['n >= 0'], ensures=['ans == n + 2'])
def inc2(n: int) -> int:
    x = inc(n)
    return inc(x)


@verify(requires=['n >= 0'], ensures=['ans >= n'])
def rec_sum(n: int) -> int:
    if n == 0:
        return 0
    return n + rec_sum(n - 1)


vp.verify_all()


