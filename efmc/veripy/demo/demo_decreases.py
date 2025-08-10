import efmc.veripy as vp
from efmc.veripy import verify, invariant

vp.enable_verification()
vp.scope('decreases')

@verify(requires=['n >= 0'], ensures=['ans == 0'], decreases='n')
def countdown(n: int) -> int:
    ans = 0
    while n > 0:
        invariant('n >= 0')
        n = n - 1
    return ans

vp.verify_all()


