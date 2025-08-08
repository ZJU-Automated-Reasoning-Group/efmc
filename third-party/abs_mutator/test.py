#!/usr/bin/env python
# encoding: utf-8

import sympy
import random
from diglib.helpers.miscs import Miscs
import os
from diglib import alg
import time
from pathlib import Path
import logging
from diglib.helpers.z3utils import Z3
import walk_sample
import numpy as np

# trace file
trace_file = "/tmp/trace.csv"
pos_vars = []

def init():

    # disable all log
    logging.disable(logging.CRITICAL)

def write_to_file(X, Y, pos):

    f = open(trace_file, 'w')

    assert(len(X[0]) == len(pos))

    # inv
    # pos = [1, 30, 44, 55, 123...]
    # vtrace1; I q; I r; I a; I b; I x; I y;
    inv = "vtrace1"
    for p in pos:
        inv += "; I x_{}".format(str(p))
        pos_vars.append("x_{}".format(str(p)))
    for i in range(0, len(Y[0])):
        inv += "; I y_{}".format(str(i))
        pos_vars.append("y_{}".format(str(i)))
    f.write(inv + "\n")

    # vtrace
    # X = [[2, 3, 4, 5, 6...], [2, 3, 4, 5, 6...], [2, 3, 4, 5, 6...]]
    # Y = [[2, 3, 4...], [2, 3, 4...], [2, 3, 4...]]
    # vtrace1; 0; 282; 8; 64; 282; 8
    trace_num = len(X)
    for i in range(0, trace_num):

        trace = "vtrace1"

        x_i = X[i]
        y_i = Y[i]

        for x in x_i:
            trace += "; {}".format(x)
        for y in y_i:
            trace += "; {}".format(y)

        f.write(trace + "\n")

    f.close()

def get_coeff(invs):

    eq_rhs = []
    eq = []
    for inv in invs:
        s = str(inv)
        expr = sympy.parse_expr(s)

        # sympy cannot parse ==
        if expr == False:
            l = s.split(" ")
            if len(l) == 3 and l[1] == "==":
                rhs = int(l[2])
                eq_rhs.append(rhs)

                colist = []
                for var in pos_vars:
                    if l[0] == sympy.symbols(var):
                        colist.append(1)
                    else:
                        colist.append(0)
                eq.append(colist)

            else:
                continue
        else:

            rhs = expr.rhs
            if rhs.is_integer:
                eq_rhs.append(int(expr.rhs))
            else:
                continue

            colist = []
            coes = expr.lhs.as_coefficients_dict()
            for var in pos_vars:
                sym = sympy.symbols(var)
                if sym in coes:
                    colist.append(int(coes[sym]))
                else:
                    colist.append(0)
            eq.append(colist)

    return eq_rhs, eq

def runDig(X, Y, pos):

    if len(X) == 0:
        return

    # write file
    #write_to_file(X, Y, pos)

    # file read
    inp = Path(trace_file)

    # run dig
    dig = alg.DigTraces.mk(inp, None)
    dinvs = dig.start(seed=round(time.time(), 2), maxdeg=None)

    loc = list(dinvs.keys())[0]
    cinvs = dinvs[loc].cinvs

    leq_rhs, leq = get_coeff(cinvs.octs)
    eq_rhs, eq = get_coeff(cinvs.eqts)

    if len(eq) == 0:
        eq_rhs.append(0)
        eq.append([0] * len(pos_vars))

    if len(leq) == 0:
        leq_rhs.append(0)
        leq.append([0] * len(pos_vars))

    leq_rhs = np.array(leq_rhs)
    leq = np.array(leq)
    eq_rhs = np.array(eq_rhs)
    eq = np.array(eq)

    res = []
    try:
        res = walk_sample.sample(eq, eq_rhs, leq, leq_rhs, 1)
    except:
        pass

    for r in res:
        print(r)

X = [[2, 3, 4, 5, 6], [2, 3, 4, 5, 6], [2, 3, 4, 5, 6]]
Y = [[2, 3, 4], [2, 3, 4], [2, 3, 4]]
pos = [1, 30, 44, 55, 123]
init()
runDig(X, Y, pos)