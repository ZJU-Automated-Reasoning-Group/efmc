# coding: utf-8
import itertools
import logging
from timeit import default_timer as symabs_timer

import z3

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
        """
        Simplify self.formula before the optimization
        """
        if self.initialized:
            simp_start = symabs_timer()
            tac = z3.Then("simplify", "propagate-values")
            simp_formula = tac.apply(self.formula).as_expr()
            simp_end = symabs_timer()
            if simp_end - simp_start > 6:
                print("error: simplification takes more than 6 seconds!!!")
            self.formula = simp_formula
        else:
            print("error: not initialized")

    def init_from_fml(self, fml: z3.BoolRef, cared_vars: [z3.ExprRef]):
        try:
            self.formula = fml
            # for var in get_variables(self.formula):
            #    if is_int(var) or is_real(var): self.vars.append(var)
            # TODO: For verification, we may only care about the primed variables
            for var in cared_vars: self.vars.append(var)

            self.initialized = True
            self.omt_engine.init_from_fml(fml)

        except z3.Z3Exception as ex:
            print("error when initialization")
            print(ex)  # TODO: should throw ex?

    def to_omt_file(self, abs_type: str) -> str:
        s = z3.Solver()
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

    def interval_abs(self) -> z3.ExprRef:
        """Interval abstraction"""
        if self.omt_engine.compact_opt:
            multi_queries = []
            for var in self.vars:
                multi_queries.append(var)
            return self.omt_engine.min_max_many(multi_queries)
        # Begin of "else"
        cnts = []
        for i in range(len(self.vars)):
            vmin = self.omt_engine.min_once(self.vars[i])
            vmax = self.omt_engine.max_once((self.vars[i]))
            # print(self.vars[i], "[", vmin, ", ", vmax, "]")
            cnts.append(z3.And(self.vars[i] >= vmin, self.vars[i] <= vmax))

        return z3.And(cnts)
        # return simplify(And(cnts))

    def zone_abs(self) -> z3.ExprRef:
        """Zone abstraction"""
        zones = list(itertools.combinations(self.vars, 2))
        if self.omt_engine.compact_opt:
            multi_queries = []
            for v1, v2 in zones:
                multi_queries.append(v1 - v2)

            return z3.simplify(self.omt_engine.min_max_many(multi_queries))
        # Begin of "else"
        zone_cnts = []
        objs = []
        for v1, v2 in zones:
            objs.append(v1 - v2)
        for exp in objs:
            exmin = self.omt_engine.min_once(exp)
            exmax = self.omt_engine.max_once(exp)
            zone_cnts.append(z3.And(exp >= exmin, exp <= exmax))
        return z3.And(zone_cnts)

    def octagon_abs(self) -> z3.ExprRef:
        """Octagon abstraction"""
        octagons = list(itertools.combinations(self.vars, 2))
        if self.omt_engine.compact_opt:
            multi_queries = []
            for v1, v2 in octagons:
                multi_queries.append(v1 - v2)
                multi_queries.append(v1 + v2)
            return self.omt_engine.min_max_many(multi_queries)
        # Begin of "else"
        oct_cnts = []
        objs = []
        for v1, v2 in octagons:
            objs.append(v1 - v2)
            objs.append(v1 + v2)

        for exp in objs:
            exmin = self.omt_engine.min_once(exp)
            exmax = self.omt_engine.max_once(exp)
            # TODO: this is not elegant (OptiMathSAT already returns an assertion)
            oct_cnts.append(z3.And(exp >= exmin, exp <= exmax))

        return z3.And(oct_cnts)
        # return simplify(And(oct_cnts))


def feat_test_counting():
    x, y, z = z3.Ints("x y z")
    fml = z3.And(x < 10, y > 133)
    sa = NumericalAbstraction()
    sa.init_from_fml(fml, [x, y])
    # sa.do_simplification()
    print(sa.interval_abs())
    # sa.zone_abs()
    # sa.octagon_abs()

# feat_test_counting()
