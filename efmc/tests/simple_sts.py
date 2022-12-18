"""
A set of simple transition systems for unit testing
"""

import z3


def get_int_sys1():
    """
     # Simple, 2-variable counter x'=x+2, and y'=y-2. 0<=x,y<=8.
       Loop back at 8 and 0. _p_x denotes primed version of x.
    """
    x, y, _p_x, _p_y = z3.Ints('x y x! y!')
    init = z3.And(x == 0, y == 8)
    trans = z3.Or(z3.And(x < 8, y <= 8, _p_x == x + 2, _p_y == y - 2), z3.And(x == 8, _p_x == 0, y == 0, _p_y == 8))
    post = z3.Not(z3.And(x == 0, y == 0))  # Is valid.
    all_vars = [x, y, _p_x, _p_y]
    return all_vars, init, trans, post


def get_int_sys2():
    x, l, _p_x, _p_l = z3.Ints('x l x! l!')
    init = z3.And(x == 0, l == 0)
    trans = z3.Or(
        z3.And(l == 0, z3.Or(z3.And(x < 10, _p_x == x + 1, _p_l == l), z3.And(x >= 10, _p_l == 1, _p_x == x))),
        z3.And(l == 1, _p_x == x, _p_l == l))
    # TS with explicit limit for x, use for testing push forward.
    # Use this prop to test push fwd. Is invalid.
    post = z3.Or(z3.And(l == 1, x > 10), l == 0)
    all_vars = [x, l, _p_x, _p_l]
    return all_vars, init, trans, post


def get_int_sys3():
    """ Simple loop: Same as above, but loop bound is symbolic(k) instead of 10."""
    x, l, k, _p_x, _p_l, _p_k = z3.Ints('x l k x! l! k!')
    init = z3.And(x == 0, l == 0, k >= 0)  # Doesn't work for init = z3.And(x==0,l==0) since k can be negative.
    trans = z3.And(_p_k == k, z3.Or(
        z3.And(l == 0, z3.Or(z3.And(x < k, _p_x == x + 1, _p_l == l), z3.And(x >= k, _p_l == 1, _p_x == x))),
        z3.And(l == 1, _p_x == x, _p_l == l)))
    post = z3.Or(z3.And(l == 1, x > k), l == 0)  # This isn't valid.
    all_vars = [x, l, k, _p_x, _p_l, _p_k]
    return all_vars, init, trans, post


def get_int_sys4():
    """ Simple loop: Same as above, but loop bound is symbolic(k) instead of 10."""
    x, l, k, _p_x, _p_l, _p_k = z3.Ints('x l k x! l! k!')
    init = z3.And(x == 0, l == 0, k >= 0)  # Doesn't work for init = z3.And(x==0,l==0) since k can be negative.
    trans = z3.And(_p_k == k, z3.Or(
        z3.And(l == 0, z3.Or(z3.And(x < k, _p_x == x + 1, _p_l == l), z3.And(x >= k, _p_l == 1, _p_x == x))),
        z3.And(l == 1, _p_x == x, _p_l == l)))
    post = z3.Or(z3.And(l == 1, x == k), l == 0)  # This is valid!
    all_vars = [x, l, k, _p_x, _p_l, _p_k]
    return all_vars, init, trans, post


def get_int_sys5():
    """Simple_vardep program from SV-COMP."""
    i, j, k, l, _p_i, _p_j, _p_k, _p_l = z3.Ints('i j k l i! j! k! l!')
    init = z3.And(i == 0, j == 0, k == 0, l == 0)
    trans = z3.Or(z3.And(l == 0, z3.Or(z3.And(k < 100, _p_i == i + 1, _p_j == j + 2, _p_k == k + 3, _p_l == l),
                                       z3.And(k >= 100, _p_i == i, _p_j == j, _p_k == k, _p_l == 1))),
                  z3.And(l == 1, _p_i == i, _p_j == j, _p_k == k, _p_l == l))
    post = z3.And(k == 3 * i, j == 2 * i)  # This is valid.
    all_vars = [i, j, k, l, _p_i, _p_j, _p_k, _p_l]
    return all_vars, init, trans, post


def get_int_sys6():
    """Simple_vardep program from SV-COMP."""
    i, j, k, l, _p_i, _p_j, _p_k, _p_l = z3.Ints('i j k l i! j! k! l!')
    init = z3.And(i == 0, j == 0, k == 0, l == 0)
    trans = z3.Or(z3.And(l == 0, z3.Or(z3.And(k < 100, _p_i == i + 1, _p_j == j + 2, _p_k == k + 3, _p_l == l),
                                       z3.And(k >= 100, _p_i == i, _p_j == j, _p_k == k, _p_l == 1))),
                  z3.And(l == 1, _p_i == i, _p_j == j, _p_k == k, _p_l == l))
    post = z3.Or(l == 0, k > 3 * i)  # Not valid.
    all_vars = [i, j, k, l, _p_i, _p_j, _p_k, _p_l]
    return all_vars, init, trans, post
