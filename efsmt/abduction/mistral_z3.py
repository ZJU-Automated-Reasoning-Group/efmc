# coding: utf-8
from z3 import *
from typing import FrozenSet
from z3.z3util import get_vars

"""
Minimal Satisfying Assignment. adapted from algo.by Alessandro Previti, Alexey S. Ignatiev
"""


# ==============================================================================
class MSASolver:
    """
    Mistral solver class.
    """

    def __init__(self, verbose=1):
        """
        Constructor.
        """
        self.formula = None
        # self.formula = simplify(self.formula)
        self.fvars = None
        self.verb = verbose

    def init_from_file(self, filename: str) -> None:
        self.formula = And(parse_smt2_file(filename))
        # self.formula = simplify(self.formula)
        self.fvars = frozenset(get_vars(self.formula))

        if self.verb > 2:
            print('c formula: \'{0}\''.format(self.formula))

    def init_from_formula(self, formula: BoolRef) -> None:
        self.formula = formula
        # self.formula = simplify(self.formula)
        self.fvars = frozenset(get_vars(self.formula))

        if self.verb > 2:
            print('c formula: \'{0}\''.format(self.formula))

    def validate_small_model(self, model: z3.ModelRef):
        decls = model.decls()
        model_cnts = []
        for var in get_vars(self.formula):
            if var.decl() in decls:
                model_cnts.append(var == model[var])
        # print(model_cnts)
        # check entailment
        s = Solver()
        s.add(Not(Implies(And(model_cnts), self.formula)))
        if s.check() == z3.sat:
            return False
        return True

    def find_small_model(self):
        """
        This method implements find_msa() procedure from Fig. 2
        of the dillig-cav12 paper.
        """
        # testing if formula is satisfiable
        s = Solver()
        s.add(self.formula)
        if s.check() == unsat:
            return False

        mus = self.compute_mus(frozenset([]), self.fvars, 0)

        model = self.get_model_forall(mus)
        return model
        # return ['{0}={1}'.format(v, model[v]) for v in frozenset(self.fvars) - mus]

    def compute_mus(self, X: FrozenSet, fvars: FrozenSet, lb: int):
        """
        Algorithm implements find_mus() procedure from Fig. 1
        of the dillig-cav12 paper.
        """

        if not fvars or len(fvars) <= lb:
            return frozenset()

        best = set()
        x = frozenset([next(iter(fvars))])  # should choose x in a more clever way

        if self.verb > 1:
            print('c state:', 'X = {0} + {1},'.format(list(X), list(x)), 'lb =', lb)

        if self.get_model_forall(X.union(x)):
            Y = self.compute_mus(X.union(x), fvars - x, lb - 1)

            cost_curr = len(Y) + 1
            if cost_curr > lb:
                best = Y.union(x)
                lb = cost_curr

        Y = self.compute_mus(X, frozenset(fvars) - x, lb)
        if len(Y) > lb:
            best = Y

        return best

    def get_model_forall(self, x_univl):
        s = Solver()
        if len(x_univl) >= 1:
            qfml = ForAll(list(x_univl), self.formula)
        else:
            qfml = self.formula  # TODO: is this OK?
        s.add(qfml)
        if s.check() == sat:
            return s.model()
        return False


if __name__ == "__main__":
    a, b, c, d = Ints('a b c d')
    fml = Or(And(a == 3, b == 3), And(a == 1, b == 1, c == 1, d == 1))
    ms = MSASolver()
    ms.init_from_formula(fml)
    print(ms.find_small_model())  # a = 3, b = 3
    # qfml = ForAll([c, d], fml)
    # s = Solver()
    # s.add(qfml)
    # s.check()
    # print(s.model())  # [a = 3, b = 3]
