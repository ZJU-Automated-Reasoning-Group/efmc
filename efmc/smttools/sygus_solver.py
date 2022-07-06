# coding: utf-8
"""
TODO (this could be very useful, but we have not used it for know):
 1. Build SyGuS instances (PBE and other constraints)
 2. Call CVC5 to solve the SyGuS instances
 3. Parse function definition from SyGuS result
 4. Map the result to Z3py world? (or PySMT world)
"""

from typing import List

import z3


def visitor(exp, seen):
    if exp in seen:
        return
    seen[exp] = True
    yield exp
    if z3.is_app(exp):
        for ch in exp.children():
            for exp in visitor(ch, seen):
                yield exp
        return
    if z3.is_quantifier(exp):
        for exp in visitor(exp.body(), seen):
            yield exp
        return


def modify(expression, fn):
    seen = {}

    def visit(exp):
        if exp in seen:
            pass
        elif fn(exp) is not None:
            seen[exp] = fn(exp)
        elif z3.is_and(exp):
            chs = [visit(ch) for ch in exp.children()]
            seen[exp] = z3.And(chs)
        elif z3.is_or(exp):
            chs = [visit(ch) for ch in exp.children()]
            seen[exp] = z3.Or(chs)
        elif z3.is_app(exp):
            chs = [visit(ch) for ch in exp.children()]
            seen[exp] = exp.decl()(chs)
        elif z3.is_quantifier(exp):
            # Note: does not work for Lambda that requires a separate case
            body = visit(exp.body())
            is_forall = exp.is_forall()
            num_pats = exp.num_patterns()
            pats = (z3.Pattern * num_pats)()
            for ii in range(num_pats):
                pats[ii] = exp.pattern(ii).ast

            num_decls = exp.num_vars()
            sorts = (z3.Sort * num_decls)()
            names = (z3.Symbol * num_decls)()
            for ii in range(num_decls):
                sorts[ii] = exp.var_sort(ii).ast
                names[ii] = z3.to_symbol(exp.var_name(ii), exp.ctx)
            r = z3.QuantifierRef(
                z3.Z3_mk_quantifier(exp.ctx_ref(), is_forall, exp.weight(), num_pats, pats, num_decls, sorts, names,
                                    body.ast),
                exp.ctx)
            seen[exp] = r
        else:
            seen[exp] = exp
        return seen[exp]

    return visit(expression)


def build_sygus_cnt(funcs: List[z3.FuncDeclRef], cnts: List[z3.BoolRef], variables: [z3.ExprRef], logic="ALL"):
    """
    Translate specification (written with z3 expr) to SyGuS format
    :param: funcs: a list of function to be synthesized
    :param: cnts: a list of constraints
    :param: vars: a list of variables
    """
    cmds = ["(set-logic {})".format(logic)]

    # target functions
    for func in funcs:
        target = "(synth-fun {} (".format(func.name())
        for ii in range(func.arity()):
            target += "({} {}) ".format(str(variables[ii]), func.domain(ii).sexpr())
        target += ") {})".format(func.range().sexpr())  # return value
        cmds.append(target)
    # variables
    for var in variables:
        cmds.append("(declare-var {} {})".format(var, var.sort().sexpr()))
    # constraints
    for c in cnts:
        cmds.append("(constraint {})".format(c.sexpr()))
    cnt = "\n".join(cmds)
    # (check-synth) to be added
    return cnt


def replace_fun_with_synthesized_one(formula, func_to_rep, func_def):
    """
    :param: fml:
    :param: cnts: a list of constraints
    :param: vars: a list of variables
    """

    def update(exp):
        if z3.is_app(exp) and z3.eq(exp.decl(), func_to_rep):
            return z3.substitute_vars(func_def, (exp.arg(0)), exp.arg(1))
        return None

    return modify(formula, update)


if __name__ == "__main__":
    x, y = z3.Ints('x y')
    fml = x + x + y > 2

    s = z3.SolverFor("HORN")
    inv = z3.Function('inv', z3.IntSort(), z3.IntSort(), z3.BoolSort())
    i, ip, j, jp = z3.Ints('i ip j jp')
    s.add(z3.ForAll([i, j], z3.Implies(i == 0, inv(i, j))))
    s.add(z3.ForAll([i, ip, j, jp], z3.Implies(z3.And(inv(i, j), i < 10, ip == i + 1), inv(ip, jp))))
    s.add(z3.ForAll([i, j], z3.Implies(z3.And(inv(i, j), i >= 10), i == 10)))

    a0, a1, a2 = z3.Ints('a0 a1 a2')
    b0, b1, b2 = z3.Ints('b0 b1 b2')
    x = z3.Var(0, z3.IntSort())
    y = z3.Var(1, z3.IntSort())
    template = z3.And(a0 + a1 * x + a2 * y >= 0, b0 + b1 * x + b2 * y >= 0)

    chc = z3.And(s.assertions())
    print(replace_fun_with_synthesized_one(chc, inv, template))

    # for f in s.assertions():
    #    f_new = modify(f, update)
    #    print(f_new)
