import efmc.veripy as vp
from efmc.veripy import verify, invariant
from typing import Dict, Set

vp.enable_verification()
vp.scope('structures')


@verify(requires=[], ensures=['ans == 2'])
def dict_insert_two() -> int:
    d: Dict[int, int] = {}
    # We do not model dict ops fully; just exercise translation
    x = 1
    y = 1
    ans = x + y
    return ans


@verify(requires=['n >= 0'], ensures=['ans >= 0'])
def set_size_lower_bound(n: int) -> int:
    s: Set[int] = set()
    i = 0
    while i < n:
        invariant('i <= n')
        i = i + 1
    # spec sugar: card(s) and mem(s, x) available in constraints
    ans = n
    return ans

vp.verify_all()


