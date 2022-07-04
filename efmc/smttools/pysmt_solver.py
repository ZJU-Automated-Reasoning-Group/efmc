# coding: utf-8
import logging

import z3
from pysmt.logics import AUTO
from pysmt.oracles import get_logic
# from pysmt.smtlib.parser import SmtLibParser
# from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import Bool, get_model, Not, Solver \
    # , qelim, ForAll
from pysmt.shortcuts import EqualsOrIff
from pysmt.shortcuts import Portfolio
from pysmt.shortcuts import Symbol, And
from pysmt.shortcuts import binary_interpolant, sequence_interpolant
from pysmt.typing import INT, REAL

"""
Augmenting Z3 using PySMT, e.g., interpolant generation
"""

logger = logging.getLogger(__name__)


# NOTE: both pysmt and z3 have a class "Solver"


def to_pysmt_vars(z3vars: [z3.ExprRef]):
    return [Symbol(v.decl().name(),
                   INT if v.is_int() else REAL) for v in z3vars]


class PySMTSolver(z3.Solver):

    def __init__(self, debug=False):
        super(PySMTSolver, self).__init__()

    @staticmethod
    def convert(zf: z3.ExprRef):
        """
        FIXME: if we do not call "pysmt_vars = ...", z3 will report naming warning..
        """
        zvs = z3.z3util.get_vars(zf)
        pysmt_vars = [Symbol(v.decl().name(), INT if v.is_int() else REAL) for v in zvs]
        z3s = Solver(name='z3')
        pysmt_fml = z3s.converter.back(zf)
        return pysmt_vars, pysmt_fml

    def check_with_pysmt(self):
        """TODO: build a Z3 model?"""
        z3fml = z3.And(self.assertions())
        pysmt_vars, pysmt_fml = PySMTSolver.convert(z3fml)
        # print(pysmt_vars)
        f_logic = get_logic(pysmt_fml)
        try:
            with Solver(logic=f_logic) as solver:
                solver.add_assertion(pysmt_fml)
                res = solver.solve()
                if res:
                    # print(solver.get_model())
                    return z3.sat
                return z3.unsat
        except Exception:
            return z3.unknown

    def check_portfolio(self):
        """
        Use multiple solvers (in parallel?)
        """
        z3fml = z3.And(self.assertions())
        pysmt_vars, pysmt_fml = PySMTSolver.convert(z3fml)
        f_logic = get_logic(pysmt_fml)

        with Portfolio([("msat", {"random_seed": 1}),
                        ("msat", {"random_seed": 17}),
                        ("msat", {"random_seed": 42}),
                        "cvc4", "yices"],
                       logic=f_logic,
                       incremental=False,
                       generate_models=False) as solver:
            solver.add_assertion(pysmt_fml)
            res = solver.solve()
            if res:
                return z3.sat
            return z3.unsat

    def all_smt(self, keys: [z3.ExprRef], bound=5):
        """Sample k models"""
        z3fml = z3.And(self.assertions())
        _, pysmt_fml = PySMTSolver.convert(z3fml)
        target_logic = get_logic(pysmt_fml)

        pysmt_var_keys = to_pysmt_vars(keys)
        # print("Target Logic: %s" % target_logic)

        with Solver(logic=target_logic) as solver:
            solver.add_assertion(pysmt_fml)
            iteration = 0
            while solver.solve():
                partial_model = [EqualsOrIff(k, solver.get_value(k)) for k in pysmt_var_keys]
                print(partial_model)
                solver.add_assertion(Not(And(partial_model)))
                iteration += 1
                if iteration >= bound: break

    def binary_interpolant(self, fml_a: z3.BoolRef, fml_b: z3.BoolRef, logic=None):
        """ Binary interpolant"""
        _, pysmt_fml_a = PySMTSolver.convert(fml_a)
        _, pysmt_fml_b = PySMTSolver.convert(fml_b)

        itp = binary_interpolant(pysmt_fml_a, pysmt_fml_b)
        return Solver(name='z3').converter.convert(itp)

    def sequence_interpolant(self, formulas: [z3.ExprRef]):
        """Sequence interpolant"""
        pysmt_formulas = []
        for fml in formulas:
            _, pysmt_fml_a = PySMTSolver.convert(fml)
            pysmt_formulas.append(pysmt_fml_a)

        seq_itp = sequence_interpolant(pysmt_formulas)
        z3_seq_itp = []
        for cnt in seq_itp:
            z3_seq_itp.append(Solver(name='z3').converter.convert(cnt))
        return z3_seq_itp

    def efsmt(self, evars: [z3.ExprRef], uvars: [z3.ExprRef], z3fml: z3.ExprRef, logic=AUTO, maxloops=None,
              esolver_name=None, fsolver_name=None,
              verbose=False):
        """Solves exists x. forall y. phi(x, y)"""

        _, phi = PySMTSolver.convert(z3fml)
        # target_logic = get_logic(pysmt_fml)
        y = to_pysmt_vars(uvars)
        y = set(y)
        x = phi.get_free_variables() - y

        with Solver(logic=logic, name=esolver_name) as esolver:

            esolver.add_assertion(Bool(True))
            loops = 0
            while maxloops is None or loops <= maxloops:
                loops += 1
                eres = esolver.solve()
                if not eres:
                    return False
                else:
                    tau = {v: esolver.get_value(v) for v in x}
                    sub_phi = phi.substitute(tau).simplify()
                    if verbose: print("%d: Tau = %s" % (loops, tau))

                    fmodel = get_model(Not(sub_phi),
                                       logic=logic, solver_name=fsolver_name)
                    if fmodel is None:
                        # a trick for returning a Z3 model
                        # TODO: in some versions, we can directly build a model object?
                        #   Another strategy is to use the converter inside pySMT?
                        for i in range(len(evars)):
                            self.add(evars[i] == esolver.get_value(list(x)[i]))
                        self.check()
                        return self.model()
                        # return tau
                    else:
                        sigma = {v: fmodel[v] for v in y}
                        sub_phi = phi.substitute(sigma).simplify()
                        if verbose: print("%d: Sigma = %s" % (loops, sigma))
                        esolver.add_assertion(sub_phi)


def test():
    x, y, z = z3.Ints("x y z")
    fml = z3.And(x > 10, y < 19, z == 3.0)
    sol = PySMTSolver()
    sol.add(fml)
    print(sol.check())
    # sol.all_smt([x, y])

    fml_a = z3.And(x <= 1, y < x)
    fml_b = z3.And(y >= z, z > 0)
    print(sol.binary_interpolant(fml_a, fml_b))
    print(sol.sequence_interpolant([fml_a, fml_b]))

# test()
