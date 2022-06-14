# coding: utf-8
import itertools
import logging
from timeit import default_timer as symabs_timer
from z3 import *
from .common import OMTEngine, OMTEngineType

"""
NOTE: This is a simplified version of the imple. in the "symabs" dir.
As we use this file to test verification idea, but not symabs algo.

To be independent, I do not import any files in this project,
"""

logger = logging.getLogger(__name__)


class NumericalAbstraction:
    """
    Symbolic Abstraction over QF_LIA and QF_LRA
    """

    def __init__(self):
        self.initialized = False
        self.formula = None
        self.vars = []
        self.omt_engine = OMTEngine()

    def set_omt_engine_type(self, ty: OMTEngineType):
        self.omt_engine.engine_type = ty

    def do_simplification(self):
        if self.initialized:
            simp_start = symabs_timer()
            tac = Then(Tactic("simplify"), Tactic("propagate-values"))
            simp_formula = tac.apply(self.formula).as_expr()
            simp_end = symabs_timer()
            if simp_end - simp_start > 6:
                print("error: simplification takes more than 6 seconds!!!")
            self.formula = simp_formula
        else:
            print("error: not initialized")

    def init_from_fml(self, fml: z3.BoolRef, vars: [z3.ExprRef]):
        try:
            self.formula = fml
            # for var in get_variables(self.formula):
            #    if is_int(var) or is_real(var): self.vars.append(var)
            # For verification, we may only care about the primed variables
            for var in vars: self.vars.append(var)

            self.initialized = True

            self.omt_engine.init_from_fml(fml)

        except Z3Exception as ex:
            print("error when initialization")
            print(ex)

    def to_omt_file(self, abs_type: str):
        s = Solver()
        s.add(self.formula)
        omt_str = s.to_smt2()
        if abs_type == "interval":
            return omt_str
        elif abs_type == "zone":
            return omt_str
        elif abs_type == "octagon":
            return omt_str
        else:
            return omt_str

    def interval_abs(self):
        if self.omt_engine.compact_opt:
            multi_queries = []
            for var in self.vars:
                multi_queries.append(var)
            return self.omt_engine.min_max_many(multi_queries)
        else:
            cnts = []
            for i in range(len(self.vars)):
                vmin = self.omt_engine.min_once(self.vars[i])
                vmax = self.omt_engine.max_once((self.vars[i]))
                # print(self.vars[i], "[", vmin, ", ", vmax, "]")
                cnts.append(And(self.vars[i] >= vmin, self.vars[i] <= vmax))

            return And(cnts)
        # return simplify(And(cnts))

    def zone_abs(self):
        zones = list(itertools.combinations(self.vars, 2))
        if self.omt_engine.compact_opt:
            multi_queries = []
            for v1, v2 in zones:
                multi_queries.append(v1 - v2)

            return simplify(self.omt_engine.min_max_many(multi_queries))
        else:
            zone_cnts = []
            objs = []
            for v1, v2 in zones:
                objs.append(v1 - v2)
            for exp in objs:
                exmin = self.omt_engine.min_once(exp)
                exmax = self.omt_engine.max_once(exp)
                zone_cnts.append(And(exp >= exmin, exp <= exmax))
            return And(zone_cnts)
        # return simplify(And(zone_cnts))

    def octagon_abs(self):
        octagons = list(itertools.combinations(self.vars, 2))
        if self.omt_engine.compact_opt:
            multi_queries = []
            for v1, v2 in octagons:
                multi_queries.append(v1 - v2)
                multi_queries.append(v1 + v2)

            return self.omt_engine.min_max_many(multi_queries)
        else:
            oct_cnts = []
            objs = []
            for v1, v2 in octagons:
                objs.append(v1 - v2)
                objs.append(v1 + v2)

            for exp in objs:
                exmin = self.omt_engine.min_once(exp)
                exmax = self.omt_engine.max_once(exp)
                # TODO: this is not elegant (OptiMathSAT already returns an assertion)
                oct_cnts.append(And(exp >= exmin, exp <= exmax))

            return And(oct_cnts)
            # return simplify(And(oct_cnts))


def feat_test_counting():
    x, y, z = Ints("x y z")
    fml = And(x < 10, y > 133)
    sa = NumericalAbstraction()
    sa.init_from_fml(fml, [x, y])
    # sa.do_simplification()
    print(sa.interval_abs())
    # sa.zone_abs()
    # sa.octagon_abs()

# feat_test_counting()
