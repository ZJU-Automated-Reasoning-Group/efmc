import pdb
from functools import reduce
from math import gcd
import typing
from beartype import beartype

import sympy
import z3

import diglib.settings as settings
import diglib.helpers.vcommon as CM
from diglib.helpers.miscs import Miscs
from diglib.helpers.z3utils import Z3
import diglib.infer.inv
import diglib.infer.infer
import diglib.data.traces


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class MyCongruence(typing.NamedTuple):
    """
    a === b (mod n)

    x == 0 (mod 4)      #0,4,8,12,..
    x + y == 1 (mod 5)   # 1,6,11,16 ...
    """
    a: sympy.Expr
    b: int
    n: int

    @beartype
    def __str__(self):
        s = f"{self.a} === {self.b} (mod {self.n})"
        return s

    @beartype
    @property
    def expr(self):
        """
        # x === 2 (mod 5) ~   x % 5 == 2
        """
        a = Z3.parse(str(self.a))
        b = Z3.parse(str(self.b))
        c = Z3.parse(str(self.n))
        return a % c == b

    @beartype
    def _eval(self, trace: diglib.data.traces.Trace):
        v = int(self.a.xreplace(trace.mydict))
        b = (v % self.n) == self.b
        return b


class Congruence(diglib.infer.inv.Inv):
    
    @beartype
    def __init__(self, mycongruence, stat=None):
        assert isinstance(mycongruence, MyCongruence), mycongruence

        super().__init__(mycongruence, stat)

    @beartype
    @classmethod
    def mk(cls, term, b, n):
        return cls(MyCongruence(term, b, n))

    @beartype
    @property
    def mystr(self):
        return str(self.inv)

    @property
    def expr(self):
        return self.inv.expr

    def test_single_trace(self, trace: diglib.data.traces.Traces):
        assert isinstance(trace, diglib.data.traces.Trace), trace
        b = self.inv._eval(trace)
        return b


class Infer(diglib.infer.infer._Infer):

    def gen(self):

        locs = self.prog.locs
        tasks = [(loc, self._get_init_traces(loc)) for loc in locs]

        return diglib.infer.inv.DInvs()

    def _get_init_traces(self, loc):
        pass

    @classmethod
    def gen_from_traces(cls, traces, symbols):
        ps = []
        terms = Miscs.get_terms_fixed_coefs(
            symbols.symbolic, settings.ITERMS, settings.ICOEFS)
        for term in terms:
            term_vals = diglib.infer.inv.RelTerm(term).eval_traces(traces)
            if len(set(term_vals)) == 1:  # all are same
                continue
            b, n = cls._solve(term_vals)
            if b is None:
                continue
            p = Congruence.mk(term, b, n)
            ps.append(p)

        return ps

    @classmethod
    def _solve(cls, X: typing.List[int]):
        assert(X), X
        b = None
        Y = [X[0] - v for v in X]
        g = reduce(gcd, Y)
        if g == 1 or g == -1:
            g = None
        else:
            b = X[0] % g
        return b, g


if __name__ == "__main__":
    import doctest
    doctest.testmod()
