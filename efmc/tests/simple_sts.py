"""
A set of simple transition systems for testing verification algorithms
(NOTE: only for integer variables)

get_int_sys1():
    # Simple, 2-variable counter x'=x+2, and y'=y-2. 0<=x,y<=8.
       Loop back at 8 and 0. _p_x denotes primed version of x.
get_int_sys2():
    x, l, _p_x, _p_l = z3.Ints('x l x! l!')
    init = z3.And(x == 0, l == 0)
    trans = z3.Or(
get_int_sys3():
    # Simple loop: Same as above, but loop bound is symbolic(k) instead of 10.
    # Label: buggy
get_int_sys4():
    # Simple loop: Same as above, but loop bound is symbolic(k) instead of 10.
get_int_sys5():
    # Simple_vardep program from SV-COMP.
get_int_sys6():
    # Simple_vardep program from SV-COMP.
get_int_sys7():
    # A counter system with multiple variables and invariant properties.
    # x increases by 1, y by 2, and z by 3 in each step until x reaches 10.
    # The invariant property is that z = 3x and y = 2x always holds.
get_int_sys8():
    # A mutual exclusion-like system with two processes.
    # pc1, pc2 are program counters for two processes.
    # The safety property is that they cannot be in critical section simultaneously.
get_int_sys9():
    # A ticket lock system with two counters.
    # 'ticket' is the next available number
    # 'serving' is the currently served number
    # The property is that ticket is always >= serving
"""

import z3

from efmc.sts import TransitionSystem


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
    """ Simple loop: Same as above, but loop bound is symbolic(k) instead of 10.
    Label: buggy
    """
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

def get_int_sys7():
    """
    A counter system with multiple variables and invariant properties.
    x increases by 1, y by 2, and z by 3 in each step until x reaches 10.
    The invariant property is that z = 3x and y = 2x always holds.
    """
    x, y, z, _p_x, _p_y, _p_z = z3.Ints('x y z x! y! z!')
    init = z3.And(x == 0, y == 0, z == 0)
    trans = z3.Or(
        z3.And(x < 10, 
               _p_x == x + 1,
               _p_y == y + 2,
               _p_z == z + 3),
        z3.And(x >= 10,
               _p_x == x,
               _p_y == y,
               _p_z == z)
    )
    post = z3.And(z == 3 * x, y == 2 * x)  # Valid invariant
    all_vars = [x, y, z, _p_x, _p_y, _p_z]
    return all_vars, init, trans, post

def get_int_sys8():
    """
    A mutual exclusion-like system with two processes.
    pc1, pc2 are program counters for two processes.
    The safety property is that they cannot be in critical section simultaneously.
    """
    pc1, pc2, _p_pc1, _p_pc2 = z3.Ints('pc1 pc2 pc1! pc2!')
    # States: 0=idle, 1=trying, 2=critical
    init = z3.And(pc1 == 0, pc2 == 0)
    
    # Process 1 transitions
    p1_to_try = z3.And(pc1 == 0, _p_pc1 == 1, _p_pc2 == pc2)
    p1_to_crit = z3.And(pc1 == 1, pc2 != 2, _p_pc1 == 2, _p_pc2 == pc2)
    p1_to_idle = z3.And(pc1 == 2, _p_pc1 == 0, _p_pc2 == pc2)
    
    # Process 2 transitions
    p2_to_try = z3.And(pc2 == 0, _p_pc2 == 1, _p_pc1 == pc1)
    p2_to_crit = z3.And(pc2 == 1, pc1 != 2, _p_pc2 == 2, _p_pc1 == pc1)
    p2_to_idle = z3.And(pc2 == 2, _p_pc2 == 0, _p_pc1 == pc1)
    
    trans = z3.Or(p1_to_try, p1_to_crit, p1_to_idle,
                 p2_to_try, p2_to_crit, p2_to_idle)
    
    post = z3.Not(z3.And(pc1 == 2, pc2 == 2))  # Mutual exclusion property
    all_vars = [pc1, pc2, _p_pc1, _p_pc2]
    return all_vars, init, trans, post

def get_int_sys9():
    """
    A ticket lock system with two counters.
    'ticket' is the next available number
    'serving' is the currently served number
    The property is that ticket is always >= serving
    """
    ticket, serving, _p_ticket, _p_serving = z3.Ints('ticket serving ticket! serving!')
    init = z3.And(ticket == 0, serving == 0)
    
    # Either issue a new ticket or advance serving number
    trans = z3.Or(
        # Issue new ticket
        z3.And(_p_ticket == ticket + 1, _p_serving == serving),
        # Advance serving
        z3.And(serving < ticket, _p_serving == serving + 1, _p_ticket == ticket)
    )
    
    post = ticket >= serving  # Valid invariant?
    all_vars = [ticket, serving, _p_ticket, _p_serving]
    return all_vars, init, trans, post

def get_int_sys10():
    """
    A resource allocation system with bounded resources.
    'free' represents available resources
    'alloc1' and 'alloc2' represent resources allocated to two processes
    The property is that total allocated resources never exceed initial amount
    """
    free, alloc1, alloc2, _p_free, _p_alloc1, _p_alloc2 = z3.Ints('free alloc1 alloc2 free! alloc1! alloc2!')
    total = 10  # Total resources in system
    
    init = z3.And(free == total, alloc1 == 0, alloc2 == 0)
    
    # Allocation and deallocation transitions
    p1_alloc = z3.And(free >= 1, 
                      _p_free == free - 1,
                      _p_alloc1 == alloc1 + 1,
                      _p_alloc2 == alloc2)
    
    p2_alloc = z3.And(free >= 1,
                      _p_free == free - 1,
                      _p_alloc2 == alloc2 + 1,
                      _p_alloc1 == alloc1)
    
    p1_dealloc = z3.And(alloc1 >= 1,
                        _p_free == free + 1,
                        _p_alloc1 == alloc1 - 1,
                        _p_alloc2 == alloc2)
    
    p2_dealloc = z3.And(alloc2 >= 1,
                        _p_free == free + 1,
                        _p_alloc2 == alloc2 - 1,
                        _p_alloc1 == alloc1)
    
    trans = z3.Or(p1_alloc, p2_alloc, p1_dealloc, p2_dealloc)
    
    post = z3.And(free + alloc1 + alloc2 == total,  # Resource conservation
                 free >= 0, alloc1 >= 0, alloc2 >= 0)  # No negative resources
    
    all_vars = [free, alloc1, alloc2, _p_free, _p_alloc1, _p_alloc2]
    return all_vars, init, trans, post



def create_simple_sts(use_real=True):
    """
    Create a simple transition system for testing purposes.
    
    Args:
        use_real: If True, use real variables, otherwise use integer variables
    
    Returns:
        A simple TransitionSystem instance
    """
    sts = TransitionSystem()
    
    # Create variables based on the type
    if use_real:
        x, y = z3.Reals('x y')
        xp, yp = z3.Reals('x! y!')
    else:
        x, y = z3.Ints('x y')
        xp, yp = z3.Ints('x! y!')
    
    # Set up the transition system
    sts.variables = [x, y]
    sts.prime_variables = [xp, yp]
    
    # Initial condition: x >= 0 and y >= 0
    sts.init = z3.And(x >= 0, y >= 0)
    
    # Transition relation: x' = x + 1, y' = y + x
    sts.trans = z3.And(xp == x + 1, yp == y + x)
    
    # Post-condition: y >= 0
    sts.post = y >= 0
    
    return sts
