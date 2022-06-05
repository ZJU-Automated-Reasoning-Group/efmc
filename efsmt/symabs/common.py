from enum import Enum
from typing import List

import z3
from z3 import Z3Exception
from z3.z3util import get_vars


def get_variables(exp: z3.ExprRef):
    return get_vars(exp)


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
        min_res = [obj.value() for obj in min_objectives]
        max_res = [obj.value() for obj in max_objectives]

        return min_res, max_res


class OMTEngineType(Enum):
    Z3OPT = 0
    PySMT = 1


class OMTEngine:
    def __init__(self):
        self.initialized = False
        self.formula = None
        self.compact_opt = True
        self.engine_type = OMTEngineType.Z3OPT

    def minimize_with_z3opt(self, obj: z3.ExprRef):
        return optimize(self.formula, obj, minimize=True)

    def maximize_with_z3opt(self, obj: z3.ExprRef):
        return optimize(self.formula, obj, minimize=False)

    def init_from_fml(self, fml: z3.BoolRef):
        try:
            self.formula = fml
            self.initialized = True
        except Z3Exception as ex:
            print("error when initialization")
            print(ex)

    def min_once(self, exp: z3.ExprRef):
        """
        Minimize the objective exp
        """
        if self.engine_type == OMTEngineType.Z3OPT:
            # FIXME: - can be understood as negative
            return -self.maximize_with_z3opt(-exp)
        else:
            raise NotImplementedError

    def max_once(self, exp: z3.ExprRef):
        """
        Maximize the objective exp
        """
        if self.engine_type == OMTEngineType.Z3OPT:
            return self.maximize_with_z3opt(exp)
        else:
            raise NotImplementedError

    def min_max_many(self, multi_queries: List):
        """
        Boxed-OMT: compute the maximum AND minimum of queries in multi_queries

        """
        if self.engine_type == OMTEngineType.Z3OPT:
            print("fml: ", self.formula)
            print("objs: ", multi_queries, multi_queries)
            min_res, max_res = box_optimize(self.formula, minimize=multi_queries, maximize=multi_queries)
            print("box res: ", min_res, max_res)
            cnts = []
            for i in range(len(multi_queries)):
                vmin = min_res[i]
                vmax = max_res[i]
                str_vmin = str(vmin)
                str_vmax = str(vmax)
                print("vmin: ", str(vmin))
                print("vmax: ", str(vmax))
                # FIXME: how to efficiently identify oo and epsilon (the following is ugly)
                if "oo" not in str_vmin:
                    if "eps" in str_vmin:
                        cnts.append(multi_queries[i] > z3.RealVal(vmin.children()[0]))
                        # cnts.append(multi_queries[i] > vmin.children()[0])
                    else:
                        cnts.append(multi_queries[i] >= z3.RealVal(vmin))
                        # cnts.append(multi_queries[i] >= vmin)
                if "oo" not in str_vmax:
                    if "eps" in str_vmax:
                        cnts.append(multi_queries[i] < z3.RealVal(vmax.children()[0]))
                        # cnts.append(multi_queries[i] < vmax.children()[0])
                    else:
                        cnts.append(multi_queries[i] <= z3.RealVal(vmax))
                        # cnts.append(multi_queries[i] <= vmax)
            return z3.And(cnts)
        else:
            raise NotImplementedError
