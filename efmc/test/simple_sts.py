"""
Simple transition systems for unit testing
"""

from z3 import *


def get_int_sys1():
    """
     # Simple, 2-variable counter x'=x+2, and y'=y-2. 0<=x,y<=8.
       Loop back at 8 and 0. _p_x denotes primed version of x.
    """
    x, y, _p_x, _p_y = Ints('x y x! y!')
    I_orig = And(x == 0, y == 8)
    T_orig = Or(And(x < 8, y <= 8, _p_x == x + 2, _p_y == y - 2), And(x == 8, _p_x == 0, y == 0, _p_y == 8))
    P_orig = Not(And(x == 0, y == 0))  # Is valid.
    return I_orig, T_orig, P_orig


def get_int_sys2():
    x, l, _p_x, _p_l = Ints('x l x! l!')
    I_orig = And(x == 0, l == 0)
    T_orig = Or(And(l == 0, Or(And(x < 10, _p_x == x + 1, _p_l == l), And(x >= 10, _p_l == 1, _p_x == x))),
                And(l == 1, _p_x == x, _p_l == l))
    # TS with explicit limit for x, use for testing push forward.
    # Use this prop to test push fwd. Is invalid.
    P_orig = Or(And(l == 1, x > 10), l == 0)
    return I_orig, T_orig, P_orig


def get_int_sys3():
    """ Simple loop: Same as above, but loop bound is symbolic(k) instead of 10."""
    x, l, k, _p_x, _p_l, _p_k = Ints('x l k x! l! k!')
    I_orig = And(x == 0, l == 0, k >= 0)  # Dosn't work for I_orig = And(x==0,l==0) since k can be negative.
    T_orig = And(_p_k == k, Or(And(l == 0, Or(And(x < k, _p_x == x + 1, _p_l == l), And(x >= k, _p_l == 1, _p_x == x))),
                               And(l == 1, _p_x == x, _p_l == l)))
    P_orig = Or(And(l == 1, x > k), l == 0)  # This isn't valid.
    return I_orig, T_orig, P_orig


def get_int_sys4():
    """ Simple loop: Same as above, but loop bound is symbolic(k) instead of 10."""
    x, l, k, _p_x, _p_l, _p_k = Ints('x l k x! l! k!')
    I_orig = And(x == 0, l == 0, k >= 0)  # Dosn't work for I_orig = And(x==0,l==0) since k can be negative.
    T_orig = And(_p_k == k, Or(And(l == 0, Or(And(x < k, _p_x == x + 1, _p_l == l), And(x >= k, _p_l == 1, _p_x == x))),
                               And(l == 1, _p_x == x, _p_l == l)))
    P_orig = Or(And(l == 1, x == k), l == 0)  # This is valid!
    return I_orig, T_orig, P_orig


def get_int_sys5():
    """Simple_vardep program from SV-COMP."""
    i, j, k, l, _p_i, _p_j, _p_k, _p_l = Ints('i j k l i! j! k! l!')
    I_orig = And(i == 0, j == 0, k == 0, l == 0)
    T_orig = Or(And(l == 0, Or(And(k < 100, _p_i == i + 1, _p_j == j + 2, _p_k == k + 3, _p_l == l),
                               And(k >= 100, _p_i == i, _p_j == j, _p_k == k, _p_l == 1))),
                And(l == 1, _p_i == i, _p_j == j, _p_k == k, _p_l == l))
    P_orig = And(k == 3 * i, j == 2 * i)  # This is valid.
    return I_orig, T_orig, P_orig


def get_int_sys6():
    """Simple_vardep program from SV-COMP."""
    i, j, k, l, _p_i, _p_j, _p_k, _p_l = Ints('i j k l i! j! k! l!')
    I_orig = And(i == 0, j == 0, k == 0, l == 0)
    T_orig = Or(And(l == 0, Or(And(k < 100, _p_i == i + 1, _p_j == j + 2, _p_k == k + 3, _p_l == l),
                               And(k >= 100, _p_i == i, _p_j == j, _p_k == k, _p_l == 1))),
                And(l == 1, _p_i == i, _p_j == j, _p_k == k, _p_l == l))
    P_orig = Or(l == 0, k > 3 * i)  # Not valid.
    return I_orig, T_orig, P_orig
