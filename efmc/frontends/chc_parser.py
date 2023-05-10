"""
Actually, we also support replacing "inv" by a function body
TODO: so, do we need to transform the CHC to our transition system first?
"""
from __future__ import print_function

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
            for i in range(num_pats):
                pats[i] = exp.pattern(i).ast

            num_decls = exp.num_vars()
            sorts = (z3.Sort * num_decls)()
            names = (z3.Symbol * num_decls)()
            for i in range(num_decls):
                sorts[i] = exp.var_sort(i).ast
                names[i] = z3.to_symbol(exp.var_name(i), exp.ctx)
            r = z3.QuantifierRef(
                z3.Z3_mk_quantifier(exp.ctx_ref(), is_forall, exp.weight(), num_pats, pats, num_decls, sorts, names,
                                    body.ast),
                exp.ctx)
            seen[exp] = r
        else:
            seen[exp] = exp
        return seen[exp]

    return visit(expression)


def test_replace():
    """
    Replace a function named XX with a concrete definition
    This can be useful in many contexts
    """
    x, y = z3.Ints('x y')
    fml = x + x + y > 2
    seen = {}
    for exp in visitor(fml, seen):
        if z3.is_const(exp) and exp.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            print("Variable", exp)
        else:
            print(exp)

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

    # template = BoolVal(True)

    def update(expression):
        if z3.is_app(expression) and z3.eq(expression.decl(), inv):
            return z3.substitute_vars(template, (expression.arg(0)), expression.arg(1))
        return None

    chc = z3.And(s.assertions())
    print(modify(chc, update))


def ground_quantifier(qexpr):
    """
    Seems this can only handle exists x . fml, or forall x.fml?
    """
    body = qexpr.body()
    var_list = list()
    for i in range(qexpr.num_vars()):
        vi_name = qexpr.var_name(i)
        # print(vi_name)
        vi_sort = qexpr.var_sort(i)
        vi = z3.Const(vi_name, vi_sort)
        var_list.append(vi)

    list.reverse(var_list)  # TODO: is this correct??
    # print(var_list)
    body = z3.substitute_vars(body, *var_list)
    # print(body, var_list)
    return body, var_list


def test_parse():
    s = z3.SolverFor("HORN")
    inv = z3.Function('inv', z3.BitVecSort(8), z3.BoolSort())
    i, ip = z3.BitVecs('i ip', 8)
    # init
    s.add(z3.ForAll([i], z3.Implies(i == 0,
                                    inv(i))))
    # inductive
    s.add(z3.ForAll([i, ip], z3.Implies(z3.And(inv(i), i < 10, ip == i + 1),
                                        inv(ip))))
    # sufficient

    s.add(z3.ForAll([i], z3.Implies(inv(i),
                                    z3.Implies(i >= 10, i == 10))))

    print(s.to_smt2())


class CHCParser:
    """
    NOTE: we assume that the input strictly follows the SyGuS(invariant) style
        The first assertion: pre
        The second assertion: trans
        The third assertion (or "goal"): post
     Besides, the goal should be in the form of
         inv => post
     Instead of
         inv and P => post (this can be transformed to the above form)
    """
    fmls = []

    def __init__(self, inputs: str, to_real: bool):
        if to_real:
            self.to_real = True
        else:
            self.to_real = False
        self.parse_chc_string(inputs)

    def parse_chc_string(self, chc: str):
        self.fmls = z3.parse_smt2_string(chc)
        assert len(self.fmls) == 3

    def solve_with_pdr(self):
        # for debugging
        sol = z3.SolverFor("HORN")
        sol.add(self.fmls)
        print(sol)
        print("Solving with CHC")
        print(sol.check())

    def get_transition_system(self):
        # TODO: remove "inv"? (Besides, ground_quantifier may change the var order...)
        #  Also, ground_quantifier can be slow
        # from z3.z3util import get_vars
        init, vars_init = ground_quantifier(self.fmls[0])
        trans, vars_trans = ground_quantifier(self.fmls[1])
        post, vars_post = ground_quantifier(self.fmls[2])

        pure_init = init.children()[0]
        pure_trans = z3.And(trans.children()[0].children()[1:])
        if z3.is_and(post.children()[0]):
            # e.g., in the form of Implies(And(inv(i), i >= 10), i == 10)
            pure_post = z3.simplify(z3.Implies(z3.And(post.children()[0].children()[1:]), post.children()[1]))
        else:
            # e.g., in the form of Implies(inv(i), i == 10)
            pure_post = z3.simplify(post.children()[1])
        # print(pure_init, "\n", pure_trans, "\n", pure_post)
        # all_vars = get_vars(trans)
        # TODO: in some cases, vars_trans may not use all the variables?
        return vars_trans, pure_init, pure_trans, pure_post


def test_parse2():
    fml = """
(declare-fun inv ((_ BitVec 8)) Bool)
(assert
 (forall ((i (_ BitVec 8)) )(let (($x12 (inv i)))
 (let (($x13 (= i (_ bv0 8))))
 (=> $x13 $x12))))
 )
(assert
 (forall ((i (_ BitVec 8)) (ip (_ BitVec 8)) )(let (($x12 (inv ip)))
 (=> (and (inv i) (bvslt i (_ bv10 8)) (= ip (bvadd i (_ bv1 8)))) $x12)))
 )
(assert
 (forall ((i (_ BitVec 8)) )(let (($x12 (inv i)))
 (=> (and $x12 (bvsge i (_ bv10 8))) (= i (_ bv10 8)))))
 )
(check-sat)
    """
    chc = CHCParser(inputs=fml, to_real=False)
    chc.parse_chc_string(fml)
    chc.get_transition_system()


def test_parse3(filename):
    with open(filename, "r") as f:
        res = f.read()
        ss = CHCParser(res, to_real=False)
        all_vars, init, trans, post = ss.get_transition_system()
        print(all_vars)
        # ss.solve_with_pdr()


if __name__ == "__main__":
    # test_parse()
    test_parse3("../../data/regressions/chc/bv/array_max-1.smt2")
    # test_replace()
