# coding: utf-8
from z3 import *

"""
A simple implementation of K-induction (TO be ported...)
"""

debug = False

def isValid(f):
    s = Solver()
    s.add(Not(f))
    if s.check() == sat:
        # print s.model()
        return False
    else:
        return True


# assume k < N
N = 20

x = {}
y = {}
z = {}
r = {}
q = {}
n = {}

# two convenient dicts
varMap = {}
varMapRev = {}
for i in range(N):
    # assume all variables are predefined
    # define 5 variables, Int
    #
    # when encoding formula,
    # use x[0] instead of x, x[1] instead of x'
    x[i] = Int("x" + str(i))
    y[i] = Int("y" + str(i))
    z[i] = Int("z" + str(i))
    n[i] = Int("n" + str(i))
    r[i] = Int("r" + str(i))
    q[i] = Int("q" + str(i))
    if i > 0:
        varMap[i - 1] = [(x[i - 1], x[i]),
                         (y[i - 1], y[i]),
                         (r[i - 1], r[i]),
                         (q[i - 1], q[i]),
                         (n[i - 1], n[i]),
                         (z[i - 1], z[i])]
        varMapRev[i - 1] = map(lambda v: (v[1], v[0]), varMap[i - 1])


# MAIN k - induction
#
# {pre} while b do P {post}
#
# check by k-induction
#
def kInduction(k, pre, post, b, encP):
    # 1.1 base case (k = 1)
    #
    # pre => post
    if isValid(Implies(pre, post)) == False:
        if debug: print("(pre => post) not valid")
        return "failure"

    # 1.2 base cases (k > 1)
    #
    #            itper
    #         ----   ---                       stop       postper
    #         |        |                         |         |
    # (pre /\ b /\ encP /\ ... /\ b /\ encP /\ not(b)) => post
    #         |                           |
    #         -------------  --------------
    #                      it
    #
    # itper = b /\ encP, 0, 1, ..., k - 2
    itper = And(b, encP)

    # it = /\ itper = /\ (b /\ encP), 0 ... k - 2
    it = And(True)

    stop = Not(b)
    postper = post

    for i in range(k - 1):
        # update it
        it = And(it, itper)

        # update stop
        stop = substitute(stop, *varMap[i])

        # update postper
        postper = substitute(postper, *varMap[i])

        if isValid(Implies(And(pre, it, stop), postper)) == False:
            if debug: print("in base cases step", i)
            return "failure"

        # update itper
        # rename i + 1 to i + 2
        itper = substitute(itper, *varMap[i + 1])
        # rename i     to i + 1
        itper = substitute(itper, *varMap[i])

    # 2. induction step (k > 0)
    #
    #          itper
    #     -----    ----------    stop       postper
    #     |                 |      |           |
    # [ /\(post /\ b /\ encP) /\ not(b) ] => post
    #  |                    |
    #  ----------  ----------
    #            it

    # reuse the stop and update
    stop = substitute(stop, *varMap[k - 1])

    # reuse the postper and update
    postper = substitute(postper, *varMap[k - 1])

    # redefine itper = post /\ b /\ encP, 0, 1, ... k - 1
    itper = And(post, b, encP)

    # redefine it = /\ itper = /\(post /\ b /\ encP) , 0 ... k - 1
    it = And(True, itper)

    # calculate it
    for i in range(k - 1):
        # update itper
        itper = substitute(itper, *varMap[i + 1])
        itper = substitute(itper, *varMap[i])
        it = And(it, itper)

    if debug: print(it)

    if isValid(Implies(And(it, stop), postper)) == False:
        if debug: print("in induction step")
        return "failure"

    # no failure return, then return success
    return "success"


# whether this triple is valid
def tripleValid(pre, b, encP, post, inv, taginfo):
    invp = substitute(inv, *varMap[0])
    if (isValid(Implies(pre, inv)) == False
            or isValid(Implies(And(inv, b, encP), invp)) == False
            or isValid(Implies(And(inv, Not(b)), post)) == False):
        print(taginfo + " This invariant can't prove this triple.")
    else:
        print(taginfo + " The Hoare triple is valid.")


# print the least k for k-induction proof
def printLeastK(pre, post, b, encP, taginfo):
    canprove = False
    for t in range(1, N):
        if kInduction(t, pre, post, b, encP) == "success":
            print(taginfo + " can use k-induction to prove, k =", t)
            canprove = True
            break
    if canprove == False:
        print(taginfo + " can't use k-induction to prove when k <", N)


# my valid Hoare triples and explanation

# Example 1:
#
"""
Description:
It calculates q = x / y and r = x % y.
"""
#
"""
{x >= 0, y >= 0, r == x, q == 0}
while(r >= y)
    r = r - y
    q = q + 1
{x == y * q + r, r >= 0}
"""
pre = And(x[0] >= 0, y[0] >= 0, r[0] == x[0], q[0] == 0)
post = And(x[0] == y[0] * q[0] + r[0], r[0] >= 0)
b = r[0] >= y[0]
encP = And(x[0] == x[1], y[1] == y[0], r[1] == r[0] - y[0], q[1] == q[0] + 1)

inv = post

tripleValid(pre, b, encP, post, inv, "Example 1")
printLeastK(pre, post, b, encP, "Example 1")

print(varMap)
print(x)
print(y)
print(r)
print(q)
exit(0)

# Example 2:
# k >= 2 is required to prove
"""
{x == 3, z == 5, q == 5, n > 0}
while(q < n)
    t = z
    z = z + x
    x = t
    q = q + 1
{n > 0, x < z, z >= q} // z = fib(5 + n), q = n + 5
"""
#
"""
Explanation:
This program calculates Fib(n + 5), n >= 0.
For 1-induction, we will lose the pre-conditions for a loop, 
where x > 0 and z > 0.
In the induction step of 1-induction, we have counter example:
[q0 = 0,
 n0 = 1,
 z0 = 0,
 x0 = -1,
 q1 = 1,
 n1 = 1,
 x1 = 0,
 z1 = -1].
However, if we enter the loop twice, 
we can pass the value from first to second, and make the proof.
"""
pre = And(x[0] == 3, z[0] == 5, q[0] == 5, n[0] > 0)
post = And(n[0] > 0, x[0] < z[0], z[0] >= q[0])
b = q[0] < n[0]
encP = And(z[1] == x[0] + z[0], x[1] == z[0], n[1] == n[0], q[1] == q[0] + 1)

inv = And(n[0] > 0, x[0] < z[0], z[0] >= q[0], q[0] > 0, x[0] > 0)

tripleValid(pre, b, encP, post, inv, "Example 2")
printLeastK(pre, post, b, encP, "Example 2")

# Example 3
# a valid Hoare triple but k-induction cannot prove
"""
{x == 0, q == n, n >= 0}
while(q > 0)
    x = x + q
    q = q - 1
{q == 0 => x == n * (n + 1) / 2}
"""
#
"""
Explanation:
This program calculates x = 1 + 2 + 3 + ... + n, n >= 0.
K-induction doesn't work because:
    the post condition doesn't reveal information about n, and
    we will get nothing when q is non-zero.
"""
pre = And(x[0] == 0, q[0] == n[0], n[0] >= 0)
post = Implies(q[0] == 0, x[0] == n[0] * (n[0] + 1) / 2)
b = q[0] > 0
encP = And(x[1] == x[0] + q[0], q[1] == q[0] - 1, n[1] == n[0])

inv = And(x[0] == (n[0] + q[0] + 1) * (n[0] - q[0]) / 2, n[0] >= 0)

tripleValid(pre, b, encP, post, inv, "Example 3")
printLeastK(pre, post, b, encP, "Example 3")

# Example 4
# t-required-k-induction Hoare triple
# Here, x, t and y are Int, t > 0
t = 14
"""
{x = 0, y = t - 1}
while(x < t)
    y = (y + 1) mod t
    x = x + 1
{y = t - 1 or 1 < x < t}
"""
pre = And(x[0] == 0, y[0] == t - 1)
post = Or(y[0] == t - 1, And(x[0] < t, x[0] > 1))
b = x[0] < t
encP = And(x[1] == x[0] + 1, y[1] == (y[0] + 1) % t)

printLeastK(pre, post, b, encP, "Example 4")
"""
print kInduction(15, pre, post, b, encP)
print kInduction(16, pre, post, b, encP)
print kInduction(17, pre, post, b, encP)
print kInduction(18, pre, post, b, encP)
print kInduction(19, pre, post, b, encP)
"""
