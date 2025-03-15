"""
Some functions for working with Z3 uninterpreted functions.
"""

from __future__ import print_function

import z3


def visitor(exp, seen):
    """
    Traverse a Z3 expression and yield all subexpressions.
    
    Args:
        exp: Z3 expression to traverse
        seen: Dictionary to track visited expressions
        
    Yields:
        All subexpressions in the formula
    """
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
    """
    Modify a Z3 expression by applying a function to each subexpression.
    
    Args:
        expression: Z3 expression to modify
        fn: Function to apply to each subexpression
        
    Returns:
        Modified Z3 expression
    """
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


def replace_inv_with_template(chc_formula, inv_func, template):
    """
    Replace an invariant function with a concrete template in a CHC formula.
    
    Args:
        chc_formula: Z3 formula containing the invariant
        inv_func: Invariant function to replace
        template: Template to replace the invariant with
        
    Returns:
        Modified formula with the invariant replaced by the template
    """

    def update(expression):
        if z3.is_app(expression) and z3.eq(expression.decl(), inv_func):
            args = [expression.arg(i) for i in range(expression.num_args())]
            return z3.substitute_vars(template, *args)
        return None

    return modify(chc_formula, update)


def instiatiate_func_with_axioms(formula, func, axioms):
    """
    Instantiate an uninterpreted function F with axioms specified in a quantified formula (that uses the function F).

    Args:
        formula: Z3 formula containing the function
        func: Function to instantiate
        axioms: Axioms to use for instantiation

    Returns:
        Modified formula with the function instantiated
    """
    raise NotImplementedError


def instiatiate_func_with_templates(formula, func, template):
    """
    Instantiate an uninterpreted function F with a template.
    
    Similar to replace the function with a concrete definition.

    Args:
        formula: Z3 formula containing the function
        func: Function to instantiate
        template: Template to instantiate the function with
    
    Returns:
        Modified formula with the function instantiated
    """
    return formula


def test_replace():
    """
    Example of replacing a function named 'inv' with a concrete definition.
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

    chc = z3.And(s.assertions())
    print(replace_inv_with_template(chc, inv, template))


if __name__ == "__main__":
    test_replace()
