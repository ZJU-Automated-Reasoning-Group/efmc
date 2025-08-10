import efmc.veripy as vp
from efmc.veripy import verify

vp.enable_verification()
vp.scope('quantifiers')


@verify(ensures=['forall x : int :: x > 0 ==> n + x > n'])
def inc_preserves_order(n: int) -> int:
    return n


@verify(ensures=['forall x :: forall y :: x + y == y + x'])
def plus_comm() -> None:
    a = 1
    b = 2
    c = a + b
    if c < 0:
        c = 0


@verify(ensures=['forall x :: exists y :: y > x'])
def exists_greater() -> None:
    z = 0
    z = z + 1


@verify(ensures=['forall x :: forall y :: not (x and y) <==> (not x) or (not y)'])
def de_morgan() -> None:
    t: bool = True
    f: bool = False
    if t and f:
        t = False


@verify(ensures=['forall x :: (not (not x)) <==> x'])
def double_negation() -> None:
    b: bool = True
    if not b:
        b = True


vp.verify_all()


