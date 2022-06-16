# coding: utf-8
from z3 import *
from typing import List


def is_equiv(a: z3.ExprRef, b: z3.ExprRef):
    s = z3.Solver()
    s.add(a != b)
    return s.check() == z3.unsat

def optimize(fml: z3.ExprRef, obj: z3.ExprRef, minimize=False, timeout: int = 0):
    s = z3.Optimize()
    s.add(fml)
    if timeout > 0:
        s.set("timeout", timeout)
    if minimize:
        obj = s.minimize(obj)
    else:
        obj = s.maximize(obj)
    if s.check() == z3.sat:
        return obj.value()


def box_optimize(fml: z3.ExprRef, minimize: List, maximize: List, timeout: int = 0):
    s = z3.Optimize()
    s.set("opt.priority", "box")
    s.add(fml)
    if timeout > 0:
        s.set("timeout", timeout)
    min_objectives = [s.minimize(exp) for exp in minimize]
    max_objectives = [s.maximize(exp) for exp in maximize]
    if s.check() == z3.sat:
        # print(s.sexpr())
        min_res = [obj.value() for obj in min_objectives]
        max_res = [obj.value() for obj in max_objectives]

        return min_res, max_res


x, y, xp, yp = Reals("x y x! y!")

fml = And(Or(And(x <= -2, x >= -3),
             And(-1 <= x, 2 >= x),
             And(-1 <= x, 0 >= x),
             And(-1 <= x, 3 >= x),
             And(-1 <= x, 4 >= x),
             And(-1 <= x, 5 >= x),
             And(-1 <= x, 6 >= x)),
          Or(And(xp == x + 2, x < 1), And(xp == x + 1, x >= 1)))

"""
Seems to be a bug??
FIXME: maybe choose the self-compiled python packages for Z3 (then we can use newer versions...)
"""

#for i in range(3):
    # print(box_optimize(fml, [xp], [xp]))
    # print(optimize(fml, xp, minimize=True))
    # print(optimize(fml, xp, minimize=False))


a, b = Bools("a b")
fml_m = Implies(Not(a), b)
fml_n = Or(a, b)
print(is_equiv(fml_m, fml_n))