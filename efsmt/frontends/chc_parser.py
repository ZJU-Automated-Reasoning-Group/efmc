# coding: utf-8
from __future__ import print_function
from z3 import *

"""
Actually, we also support replacing "inv" by a function body
TODO: so, do we need to transform the CHC to our transition system first?
"""


def visitor(e, seen):
    if e in seen:
        return
    seen[e] = True
    yield e
    if is_app(e):
        for ch in e.children():
            for e in visitor(ch, seen):
                yield e
        return
    if is_quantifier(e):
        for e in visitor(e.body(), seen):
            yield e
        return


def modify(e, fn):
    seen = {}

    def visit(e):
        if e in seen:
            pass
        elif fn(e) is not None:
            seen[e] = fn(e)
        elif is_and(e):
            chs = [visit(ch) for ch in e.children()]
            seen[e] = And(chs)
        elif is_or(e):
            chs = [visit(ch) for ch in e.children()]
            seen[e] = Or(chs)
        elif is_app(e):
            chs = [visit(ch) for ch in e.children()]
            seen[e] = e.decl()(chs)
        elif is_quantifier(e):
            # Note: does not work for Lambda that requires a separate case
            body = visit(e.body())
            is_forall = e.is_forall()
            num_pats = e.num_patterns()
            pats = (Pattern * num_pats)()
            for i in range(num_pats):
                pats[i] = e.pattern(i).ast

            num_decls = e.num_vars()
            sorts = (Sort * num_decls)()
            names = (Symbol * num_decls)()
            for i in range(num_decls):
                sorts[i] = e.var_sort(i).ast
                names[i] = to_symbol(e.var_name(i), e.ctx)
            r = QuantifierRef(
                Z3_mk_quantifier(e.ctx_ref(), is_forall, e.weight(), num_pats, pats, num_decls, sorts, names, body.ast),
                e.ctx)
            seen[e] = r
        else:
            seen[e] = e
        return seen[e]

    return visit(e)


def test_replace():
    x, y = Ints('x y')
    fml = x + x + y > 2
    seen = {}
    for e in visitor(fml, seen):
        if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
            print("Variable", e)
        else:
            print(e)

    s = SolverFor("HORN")
    inv = Function('inv', IntSort(), IntSort(), BoolSort())
    i, ip, j, jp = Ints('i ip j jp')
    s.add(ForAll([i, j], Implies(i == 0, inv(i, j))))
    s.add(ForAll([i, ip, j, jp], Implies(And(inv(i, j), i < 10, ip == i + 1), inv(ip, jp))))
    s.add(ForAll([i, j], Implies(And(inv(i, j), i >= 10), i == 10)))

    a0, a1, a2 = Ints('a0 a1 a2')
    b0, b1, b2 = Ints('b0 b1 b2')
    x = Var(0, IntSort())
    y = Var(1, IntSort())
    template = And(a0 + a1 * x + a2 * y >= 0, b0 + b1 * x + b2 * y >= 0)

    # template = BoolVal(True)

    def update(e):
        if is_app(e) and eq(e.decl(), inv):
            return substitute_vars(template, (e.arg(0)), e.arg(1))
        return None

    chc = And(s.assertions())
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
    s = SolverFor("HORN")
    inv = Function('inv', BitVecSort(8), BoolSort())
    i, ip = BitVecs('i ip', 8)
    # init
    s.add(ForAll([i], Implies(i == 0,
                              inv(i))))
    # inductive
    s.add(ForAll([i, ip], Implies(And(inv(i), i < 10, ip == i + 1),
                                  inv(ip))))
    # sufficient

    s.add(ForAll([i], Implies(inv(i),
                              Implies(i >= 10, i == 10))))

    print(s.to_smt2())


class CHCParser:
    """
    NOTE: we assume that the input strictly follows the SyGuS inv style
        The first assertion: pre
        The second assertion: trans
        The third assertion (or "goal"): post
     Besides, the goal should be in the form of
         inv => post
     Instead of
         inv and P => post (this can be be transformed to the above form)
    """
    fmls = []

    def __init__(self, inputs: str, to_real: bool):
        self.to_real = False
        self.parse_chc_string(inputs)

    def parse_chc_file(self, filename: str):
        """
        This is for parring z3's special format of CHC?
        TODO: sometimes, chc separates assertions and goal (i.g., the post-cond)?
        """
        fp = z3.Fixedpoint()
        # fp.set("print-certificate", True)
        # NOTE: important, the return value is the query.
        rules = fp.get_rules()
        queries = fp.parse_file(filename)
        assert len(rules) == 2
        assert len(queries) == 1
        for r in fp.get_rules():
            self.sol.add(r)
        self.sol.add(Not(queries[0]))

    def parse_chc_string(self, chc: str):
        self.fmls = z3.parse_smt2_string(chc)
        assert len(self.fmls) == 3

    def solve_with_pdr(self):
        # for debugging
        sol = SolverFor("HORN")
        sol.add(self.fmls)
        print(sol)
        print("Solving with CHC")
        print(sol.check())

    def get_transition_system(self):
        # TODO: remove "inv"? (Besides, ground_quantifier may change the var order...)
        # from z3.z3util import get_vars
        init, vars_init = ground_quantifier(self.fmls[0])
        trans, vars_trans = ground_quantifier(self.fmls[1])
        post, vars_post = ground_quantifier(self.fmls[2])

        pure_init = init.children()[0]
        pure_trans = z3.And(trans.children()[0].children()[1:])
        if z3.is_and(post.children()[0]):
            # e.g., in the form of Implies(And(inv(i), i >= 10), i == 10)
            pure_post = simplify(z3.Implies(z3.And(post.children()[0].children()[1:]), post.children()[1]))
        else:
            # e.g., in the form of Implies(inv(i), i == 10)
            pure_post = simplify(post.children()[1])

        # print(pure_init, "\n", pure_trans, "\n", pure_post)

        # all_vars = get_vars(trans)
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
    chc = CHCParser()
    chc.parse_chc_string(fml)
    chc.get_transition_system()


def test_parse3(filename):
    with open(filename, "r") as f:
        res = f.read()
        ss = CHCParser(res, to_real=False)
        vars, init, trans, post = ss.get_transition_system()
        print(vars)
        # ss.solve_with_pdr()


if __name__ == "__main__":
    # test_parse()
    test_parse3("../../benchmarks/bv/array_max-1.smt2")
    # test_replace()
