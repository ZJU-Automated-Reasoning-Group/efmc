from chc2c import compile_ira_to_c_sat
from z3 import *

"""
(define-fun pre_fun ((x Int) (y Int)) Bool
    (and (= x 1) (= y 1)))
(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (= x! (+ x y)) (= y! (+ x y))))
(define-fun post_fun ((x Int) (y Int)) Bool
    (>= y 1))
"""


def test():
    x, y, z = Ints("x y z")
    fml = Or(x > 3, And(x + y < 10, y - z == 8))
    compile_ira_to_c_sat(simplify(fml))


if __name__ == '__main__':
    test()