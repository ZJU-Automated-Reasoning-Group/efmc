# coding: utf-8
import z3
from z3.z3util import get_vars
from typing import List, Set


def is_function_symbol(s: z3.ExprRef) -> bool:
    """Decide"""
    if not z3.is_app(s):
        return False
    if z3.is_const(s):
        return False

    func = s.decl()
    if func.range() == z3.BoolSort():
        # predicate symbol
        return False

    if func.name().lower() == 'if':
        return False

    return True


def function_symbols(s: z3.ExprRef) -> Set[z3.FuncDeclRef]:
    """Find function symbols in a Z3 expr"""
    fsymbols = set()
    if is_function_symbol(s):
        fsymbols.add(s.decl())

    for child in s.children():
        fsymbols.update(function_symbols(child))

    return fsymbols


def z3_skolemize(e: z3.ExprRef) -> z3.ExprRef:
    """
    Skolemize a formula (important for handling quantified formulas)
    """
    g = z3.Goal()
    g.add(e)
    t = z3.Tactic('snf')
    res = t(g)
    return res.as_expr()


def create_function_body_str(funcname: str, varlist: List, body: z3.ExprRef) -> [str]:
    """"""
    res = []
    target = "(define-fun {} (".format(funcname)
    for i in range(len(varlist)):
        target += "({} {}) ".format(str(varlist[i]), varlist[i].sort().sexpr())
    target += ") Bool {})".format(body.sexpr())  # return value
    res.append(target)

    for var in varlist:
        res.append("(declare-const {} {})".format(var, var.sort().sexpr()))
    return res


def get_variables(exp: z3.ExprRef) -> [z3.ExprRef]:
    return get_vars(exp)


def ctx_simplify(exp: z3.ExprRef):
    """Perform complex simplifications (can be slow)"""
    return z3.Tactic('ctx-solver-simplify')(exp).as_expr()


def negate(f: z3.ExprRef):
    """Negate a formula"""
    if z3.is_not(f):
        return f.arg(0)
    else:
        return z3.Not(f)


def is_valid(phi: z3.ExprRef) -> bool:
    s = z3.Solver()
    s.add(z3.Not(phi))
    if s.check() == z3.sat:
        return False
    else:
        return True


def is_entail(a: z3.ExprRef, b: z3.ExprRef):
    s = z3.Solver()
    s.add(z3.Not(z3.Implies(a, b)))
    if s.check() == z3.sat:
        return False
    else:
        return True


def is_sat(phi: z3.ExprRef):
    s = z3.Solver()
    s.add(phi)
    return s.check() == z3.sat


def is_equiv(a: z3.ExprRef, b: z3.ExprRef):
    s = z3.Solver()
    s.add(a != b)
    return s.check() == z3.unsat


def z3_string_decoder(z3str: z3.StringVal):
    length = z3.Int("length")
    tmp_string = z3.String("ts")
    solver = z3.Solver()
    solver.add(tmp_string == z3str)
    solver.add(z3.Length(tmp_string) == length)
    assert solver.check() == z3.sat

    model = solver.model()
    assert model[length].is_int()
    num_chars = model[length].as_long()

    solver.push()
    char_bvs = []
    for i in range(num_chars):
        char_bvs.append(z3.BitVec("ch_%d" % i, 8))
        solver.add(z3.Unit(char_bvs[i]) == z3.SubString(tmp_string, i, 1))

    assert solver.check() == z3.sat
    model = solver.model()
    python_string = "".join([chr(model[ch].as_long()) for ch in char_bvs])
    return python_string


def z3_value_to_python(value):
    if z3.is_true(value):
        return True
    elif z3.is_false(value):
        return False
    elif z3.is_int_value(value):
        return value.as_long()
    elif z3.is_rational_value(value):
        return float(value.numerator_as_long()) / float(value.denominator_as_long())
    elif z3.is_string_value(value):
        return z3_string_decoder(value)
    elif z3.is_algebraic_value(value):
        raise NotImplementedError()
    else:
        raise NotImplementedError()


class FormulaInfo:
    def __init__(self, fml):
        self.formula = fml
        self.has_quantifier = self.has_quantifier()
        self.logic = self.get_logic()

    def apply_probe(self, name):
        g = z3.Goal()
        g.add(self.formula)
        p = z3.Probe(name)
        return p(g)

    def has_quantifier(self):
        return self.apply_probe('has-quantifiers')

    def logic_has_bv(self):
        return "BV" in self.logic

    def get_logic(self):
        """
        TODO: how about string, array, and FP?
        """
        try:
            if not self.has_quantifier:
                if self.apply_probe("is-propositional"):
                    return "QF_UF"
                elif self.apply_probe("is-qfbv"):
                    return "QF_BV"
                elif self.apply_probe("is-qfaufbv"):
                    return "QF_AUFBV"
                elif self.apply_probe("is-qflia"):
                    return "QF_LIA"
                # elif self.apply_probe("is-quauflia"):
                #    return "QF_AUFLIA"
                elif self.apply_probe("is-qflra"):
                    return "QF_LRA"
                elif self.apply_probe("is-qflira"):
                    return "QF_LIRA"
                elif self.apply_probe("is-qfnia"):
                    return "QF_NIA"
                elif self.apply_probe("is-qfnra"):
                    return "QF_NRA"
                elif self.apply_probe("is-qfufnra"):
                    return "QF_UFNRA"
                else:
                    return "ALL"
            else:
                if self.apply_probe("is-lia"):
                    return "LIA"
                elif self.apply_probe("is-lra"):
                    return "LRA"
                elif self.apply_probe("is-lira"):
                    return "LIRA"
                elif self.apply_probe("is-nia"):
                    return "NIA"
                elif self.apply_probe("is-nra"):
                    return "NRA"
                elif self.apply_probe("is-nira"):
                    return "NIRA"
                else:
                    return "ALL"
        except Exception as ex:
            print(ex)
            return "ALL"


def get_logic(fml: z3.ExprRef):
    fml_info = FormulaInfo(fml)
    return fml_info.get_logic()
