# coding: utf-8
import itertools
import logging
from typing import List
# from z3 import *
import z3
from .common import box_optimize, get_variables

"""
Interval
Zone
Octagon
"""

logger = logging.getLogger(__name__)


def get_bv_size(x: z3.ExprRef):
    if z3.is_bv(x):
        return x.sort().size()
    else:
        return -1


class BiVecSymbolicAbstraction:
    """
    Symbolic Abstraction over BitVec (very basic version)
    """

    def __init__(self):
        self.initialized = False
        self.formula = None
        self.vars = []
        self.interval_abs_as_fml = z3.BoolVal(True)
        self.zone_abs_as_fml = z3.BoolVal(True)
        self.octagon_abs_as_fml = z3.BoolVal(True)

        self.single_query_timeout = 5000
        self.multi_query_tiemout = 0
        # self.poly_abs_as_fml = BoolVal(True)

        self.compact_opt = True

        self.obj_no_overflow = False
        self.obj_no_underflow = False

        self.signed = False
        # set_param("verbose", 15)

    def init_from_fml(self, fml: z3.BoolRef):
        try:
            self.formula = fml
            for var in get_variables(self.formula):
                if z3.is_bv(var): self.vars.append(var)
            self.initialized = True
        except z3.Z3Exception as ex:
            print("error when initialization")
            print(ex)

    def min_once(self, exp: z3.ExprRef):
        """ Minimize exp subject to self.formula"""
        sol = z3.Optimize()
        sol.set("timeout", self.single_query_timeout)
        sol.add(self.formula)
        sol.minimize(exp)
        if sol.check() == z3.sat:
            m = sol.model()
            return m.eval(exp, True)
            # return m.eval(exp).as_long()

    def max_once(self, exp: z3.ExprRef):
        """ Maximize exp subject to self.formula"""
        sol = z3.Optimize()
        sol.set("timeout", self.single_query_timeout)
        sol.add(self.formula)
        sol.maximize(exp)
        if sol.check() == z3.sat:
            m = sol.model()
            # print(m)
            return m.eval(exp, True)
            # return m.eval(exp).as_long()

    def min_max_many(self, multi_queries: List[z3.ExprRef]):
        """ Minimize and maximize multi_quries subject to self.formula"""
        # n_queries = len(multi_queries)
        # timeout = n_queries * self.single_query_timeout * 2 # is this reasonable?
        min_res, max_res = box_optimize(self.formula, minimize=multi_queries, maximize=multi_queries, timeout=30000)
        # TODO: the res of handler.xx() is not a BitVec val, but Int?
        #   what if it is a value large than the biggest integer of the size
        #   (is it possible? e.g., due to overflow)
        cnts = []
        for i in range(len(multi_queries)):
            vmin = min_res[i]
            vmax = max_res[i]
            vmin_bvval = z3.BitVecVal(vmin.as_long(), multi_queries[i].sort().size())
            vmax_bvval = z3.BitVecVal(vmax.as_long(), multi_queries[i].sort().size())
            # print(self.vars[i].sort(), vmin.sort(), vmax.sort())
            if self.signed:
                cnts.append(z3.And(multi_queries[i] >= vmin_bvval, multi_queries[i] <= vmax_bvval))
            else:
                cnts.append(z3.And(z3.UGE(multi_queries[i], vmin_bvval), z3.ULE(multi_queries[i], vmax_bvval)))
        return z3.And(cnts)

    def interval_abs(self):
        """Interval abstraction"""
        if self.compact_opt:
            multi_queries = []
            for var in self.vars:
                multi_queries.append(var)
            self.interval_abs_as_fml = self.min_max_many(multi_queries)
            return
            # print(self.interval_abs_as_fml)
        # Begin of "Else"
        cnts = []
        for i in range(len(self.vars)):
            vmin = self.min_once(self.vars[i])
            vmax = self.max_once((self.vars[i]))
            if self.signed:
                cnts.append(z3.And(self.vars[i] >= vmin, self.vars[i] <= vmax))
            else:
                cnts.append(z3.And(z3.UGE(self.vars[i], vmin), z3.ULE(self.vars[i], vmax)))
            print(self.vars[i], "[", vmin, ", ", vmax, "]")
        self.interval_abs_as_fml = z3.And(cnts)

    def zone_abs(self):
        """Zone abstraction"""
        zones = list(itertools.combinations(self.vars, 2))
        if self.compact_opt:
            multi_queries = []
            wrap_around_cnts = []
            for v1, v2 in zones:
                if v1.sort().size() == v2.sort().size():
                    multi_queries.append(v1 - v2)
                    if self.obj_no_overflow:
                        wrap_around_cnts.append(z3.BVSubNoOverflow(v1, v2))
                    if self.obj_no_underflow:
                        wrap_around_cnts.append(z3.BVSubNoUnderflow(v1, v2, signed=self.signed))

            if len(wrap_around_cnts) > 1:
                self.formula = z3.And(self.formula, z3.And(wrap_around_cnts))

            self.zone_abs_as_fml = self.min_max_many(multi_queries)
            return

        # Begin of "Else"
        zone_cnts = []
        objs = []
        wrap_around_cnts = []
        for v1, v2 in zones:
            if v1.sort().size() == v2.sort().size():
                objs.append(v1 - v2)
                if self.obj_no_overflow:
                    wrap_around_cnts.append(z3.BVSubNoOverflow(v1, v2))
                if self.obj_no_underflow:
                    wrap_around_cnts.append(z3.BVSubNoUnderflow(v1, v2, signed=self.signed))

        if len(wrap_around_cnts) > 1:
            self.formula = z3.And(self.formula, z3.And(wrap_around_cnts))

        for exp in objs:
            # TODO: use BVSubNoOverflow
            exmin = self.min_once(exp)
            exmax = self.max_once(exp)
            if self.signed:
                zone_cnts.append(z3.And(exp >= exmin, exp <= exmax))
            else:
                zone_cnts.append(z3.And(z3.UGE(exp, exmin), z3.ULE(exp, exmax)))

        self.zone_abs_as_fml = z3.And(zone_cnts)

    def octagon_abs(self):
        """Octagon abstraction"""
        octagons = list(itertools.combinations(self.vars, 2))
        if self.compact_opt:
            multi_queries = []
            wrap_around_cnts = []

            for var in self.vars:
                # need this?
                multi_queries.append(var)

            for v1, v2 in octagons:
                if v1.sort().size() == v2.sort().size():
                    multi_queries.append(v1 - v2)
                    multi_queries.append(v1 + v2)
                    if self.obj_no_overflow:
                        wrap_around_cnts.append(z3.BVSubNoOverflow(v1, v2))
                        wrap_around_cnts.append(z3.BVAddNoOverflow(v1, v2, signed=self.signed))
                    if self.obj_no_underflow:
                        wrap_around_cnts.append(z3.BVSubNoUnderflow(v1, v2, signed=self.signed))
                        wrap_around_cnts.append(z3.BVAddNoUnderflow(v1, v2))

            if len(wrap_around_cnts) > 1:
                self.formula = z3.And(self.formula, z3.And(wrap_around_cnts))

            self.octagon_abs_as_fml = self.min_max_many(multi_queries)
            return
            # print(self.zone_abs_as_fml)
        # Begin of "Else"
        oct_cnts = []
        objs = []
        wrap_around_cnts = []

        for var in self.vars:
            # need this?
            objs.append(var)

        for v1, v2 in octagons:
            if v1.sort().size() == v2.sort().size():
                objs.append(v1 - v2)
                objs.append(v1 + v2)
                if self.obj_no_overflow:
                    wrap_around_cnts.append(z3.BVSubNoOverflow(v1, v2))
                    wrap_around_cnts.append(z3.BVAddNoOverflow(v1, v2, signed=self.signed))
                if self.obj_no_underflow:
                    wrap_around_cnts.append(z3.BVSubNoUnderflow(v1, v2, signed=self.signed))
                    wrap_around_cnts.append(z3.BVAddNoUnderflow(v1, v2))

        if len(wrap_around_cnts) > 1:
            self.formula = z3.And(self.formula, z3.And(wrap_around_cnts))

        for exp in objs:
            exmin = self.min_once(exp)
            exmax = self.max_once(exp)
            if self.signed:
                oct_cnts.append(z3.And(exp >= exmin, exp <= exmax))
            else:
                oct_cnts.append(z3.And(z3.UGE(exp, exmin), z3.ULE(exp, exmax)))

        self.zone_abs_as_fml = z3.And(oct_cnts)
