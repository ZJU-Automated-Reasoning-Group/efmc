import efmc.veripy as vp
from efmc.veripy import verify, invariant

vp.enable_verification()
vp.scope('loops')

@verify(
    requires=['a >= 0', 'b >= 0'],
    ensures=['ans == a * b']
)
def mul_by_addition(a: int, b: int) -> int:
    ans = 0
    n = a
    while n > 0:
        invariant('n >= 0')
        invariant('ans == (a - n) * b')
        ans = ans + b
        n = n - 1
    return ans


@verify(
    requires=['n >= 0'],
    ensures=['ans == ((n + 1) * n) // 2']
)
def summation(n: int) -> int:
    ans = 0
    for i in range(0, n + 1):
        invariant('i <= n + 1')
        invariant('ans == i * (i - 1) // 2')
        ans = ans + i
    return ans


vp.verify_all()


