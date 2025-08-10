import efmc.veripy as vp

vp.enable_verification()
vp.scope('tmp')

@vp.verify(
    requires=['n >= 0'],
    ensures=['ans == n']
)
def counter(n: int) -> int:
    y = n
    ans = 0
    while y > 0:
        vp.invariant('ans + y == n')
        vp.invariant('y >= 0')
        ans = ans + 1
        y = y - 1
    return ans

vp.do_verification('tmp', ignore_err=False)


