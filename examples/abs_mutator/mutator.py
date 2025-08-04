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
import pickle  
import time


# trace file
trace_file = "/tmp/trace.csv"

# inference results for incremental refiment and input generation
dinvs = {}
pos_vars = []
samples = []

leq_rhs_list = []
leq_list = []
leq_prob = {}
eq_rhs_list = []
eq_list = []
eq_prob = {}

# bound the number of used invariants
inv_bound = 0

# related log
# logger = logging.getLogger("infer.log")
time_count = {'dig' : 0.0, 'post_dig' : 0.0, 'walk' : 0.0, 'dig_size' : 0, 'walk_size' : 0}

def init(seed):
    # disable all log
    # logging.disable(logging.CRITICAL)
    pass

def deinit():
    pass

def write_to_file(X, Y, pos):

    f = open(trace_file, 'w')

    assert(len(X[0]) == len(pos))
    assert(len(pos) > 0)

    # inv
    # pos = [1, 30, 44, 55, 123...]
    # vtrace1; I q; I r; I a; I b; I x; I y;
    inv = "vtrace1"
    pos_vars.clear()
    for p in pos:
        inv += "; I x_{}".format(str(p))
        pos_vars.append("x_{}".format(str(p)))
    for i in range(0, len(Y[0])):
        inv += "; I y_{}".format(str(i))
        pos_vars.append("y_{}".format(str(i)))
    f.write(inv + "\n")

    # file = open(pos_file, 'wb')
    # pickle.dump(pos_vars, file)
    # file.close()

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

def get_coeff(invs, pos):

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
                for var in pos:
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
            for var in pos:
                sym = sympy.symbols(var)
                if sym in coes:
                    colist.append(int(coes[sym]))
                else:
                    colist.append(0)
            eq.append(colist)

    return eq_rhs, eq

def runDig(X, Y, pos):

    assert(len(X) > 0)

    time_count['dig_size'] = time_count['dig_size'] + len(X)

    # write file
    write_to_file(X, Y, pos)

    # file read
    inp = Path(trace_file)

    # run dig
    try:

        start = time.time()
        dig = alg.DigTraces.mk(inp, None)
        # {'vtrace1' : invariants}
        dig_invs = dig.start(seed=round(time.time(), 2), maxdeg=None)
        time_count['dig'] = time_count['dig'] + (time.time() - start)

        start = time.time()
        dinvs.clear()
        # persist invs
        for key in dig_invs:
            dinvs[key] = dig_invs[key]

        # sample parameter
        loc = list(dinvs.keys())[0]
        cinvs = dinvs[loc].cinvs

        inv_bound = len(X[0])

        # total number of invs
        # count = len(cinvs.octs) + len(cinvs.eqts)

        leq_rhs, leq = get_coeff(cinvs.octs, pos_vars)
        eq_rhs, eq = get_coeff(cinvs.eqts, pos_vars)
        if len(eq) == 0:
            eq_rhs.append(0)
            eq.append([0] * len(pos_vars))
        if len(leq) == 0:
            leq_rhs.append(0)
            leq.append([0] * len(pos_vars))

        leq_rhs_list.clear()
        leq_list.clear()
        eq_rhs_list.clear()
        eq_list.clear()

        count = 0
        for item in leq_rhs:
            leq_rhs_list.append(item)
            leq_prob[count] = 1.0
            count = count + 1

        for item in leq:
            leq_list.append(item)      

        count = 0
        for item in eq_rhs:
            eq_rhs_list.append(item)
            eq_prob[count] = 1.0
            count = count + 1

        for item in eq:
            eq_list.append(item)

        time_count['post_dig'] = time_count['post_dig'] + (time.time() - start)
        # print(leq_rhs_list, leq_list, eq_list, eq_list)
    except:
        pass
    
def update_fitness(fitness):

    if fitness > 0:
        for index, prob in eq_prob.items():
          eq_prob[index] += 0.1    

        for index, prob in leq_prob.items():
          leq_prob[index] += 0.1
    else:
        for index, prob in eq_prob.items():
            eq_prob[index] -= 0.1
              
        for index, prob in leq_prob.items():
            leq_prob[index] -= 0.1

def mutate(buf, X, Y, pos):
    
    if len(dinvs) == 0:
        return buf  

    # if there are not enough samples, try to enlarge
    # every time 512
    start = time.time()
    if len(samples) == 0:

        # select based on prob
        leq_rhs_list_used = []
        leq_list_used = []
        eq_rhs_list_used = []
        eq_list_used = []

        for index, prob in leq_prob.items():

            if index >= len(leq_rhs_list) or index >= len(leq_list):
                break

            if prob > 0.5:
                leq_rhs_list_used.append(leq_rhs_list[index])
                leq_list_used.append(leq_list[index])

            # bound
            if len(leq_list_used) > inv_bound:
                break

        for index, prob in eq_prob.items():

            if index >= len(eq_rhs_list) or index >= len(eq_list):
                break

            if prob > 0.5:
                eq_rhs_list_used.append(eq_rhs_list[index])
                eq_list_used.append(eq_list[index])                

            # bound
            if (len(leq_list_used) + len(eq_list_used)) > inv_bound:
                break            

        leq_rhs = np.array(leq_rhs_list_used)
        leq = np.array(leq_list_used)
        eq_rhs = np.array(eq_rhs_list_used)
        eq = np.array(eq_list_used)              
        # print(leq_rhs_list, leq_list, eq_list, eq_list)
        try:
            time_count['walk_size'] = time_count['walk_size'] + 512
            walks = walk_sample.sample(eq, eq_rhs, leq, leq_rhs, 512)
            for w in walks:
                samples.append(w)
        except:
            pass

    time_count['walk'] = time_count['walk'] + (time.time() - start)

    # samples [x1, x2, x3, x4] 2 times:
    # [[1, 1, 1, 1], [2, 2, 2, 2]], each list is a set of byte values
    if len(samples) > 0:
        # print(samples)
        sample = samples.pop()
        # constructing the mutated buff
        index = 0
        for loc in pos:

            if index == len(sample):
                break

            if sample[index] < 0 or sample[index] > 256:
                buf[loc] = 0
            else:
                buf[loc] = int(sample[index])
            index += 1
    else:
        pass

    return buf

def fuzz(buf, add_buf, max_size, X, Y, pos, incremental, fitness):

    if len(pos) > 0 and incremental > 0:
        runDig(X, Y, pos)

    update_fitness(fitness)
    mutated_out = mutate(buf, X, Y, pos)
    # logger.debug("related statistic: %s" % time_count)
    print(time_count)
    return mutated_out

    
