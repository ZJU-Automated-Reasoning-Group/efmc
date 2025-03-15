"""
Some functions for working with Z3 uninterpreted functions.
"""

from __future__ import print_function
from typing import Callable, Optional
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


def modify(expression: z3.ExprRef, fn: Callable[[z3.ExprRef], Optional[z3.ExprRef]]) -> z3.ExprRef:
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


def replace_func_with_template(formula: z3.ExprRef, func: z3.FuncDeclRef, template: z3.ExprRef) -> z3.ExprRef:
    """
    Replace an uninterpreted function with a concrete template in a CHC formula.
    
    Args:
        formula: Z3 formula containing the uninterpreted function
        func: Uninterpreted function to replace
        template: Template to replace the uninterpreted function with
        
    Returns:
        Modified formula with the uninterpreted function replaced by the template
    """

    def update(expression):
        if z3.is_app(expression) and z3.eq(expression.decl(), func):
            args = [expression.arg(i) for i in range(expression.num_args())]
            return z3.substitute_vars(template, *args)
        return None

    return modify(formula, update)


def instiatiate_func_with_axioms(formula: z3.ExprRef, func: z3.FuncDeclRef, axiom: z3.ExprRef) -> z3.ExprRef:
    """
    Instantiate an uninterpreted function F with axiom specified in a quantified formula (that uses the function F).

    Args:
        formula: Z3 formula containing the function
        func: Function to instantiate
        axiom: Axiom to use for instantiation

    Returns:
        Modified formula with the function instantiated
    """
    # Find all applications of the function in the formula
    func_apps = []
    seen = {}
    
    for expr in visitor(formula, seen):
        if z3.is_app(expr) and z3.eq(expr.decl(), func):
            func_apps.append(expr)
    
    if not func_apps:
        return formula  # No instances of the function found
    
    # Check if axiom is a quantified formula
    if not z3.is_quantifier(axiom):
        raise ValueError("Axiom must be a quantified formula")
    
    # Extract the body of the axiom
    axiom_body = axiom.body()
    
    # For each function application, instantiate the axiom
    instantiated_axioms = []
    for app in func_apps:
        # Get arguments of the function application
        args = [app.arg(i) for i in range(app.num_args())]
        
        # Create substitution for the quantified variables in the axiom
        num_vars = axiom.num_vars()
        if num_vars != len(args):
            raise ValueError(f"Number of arguments in function application ({len(args)}) "
                            f"doesn't match number of quantified variables ({num_vars})")
        
        # Instantiate the axiom with the arguments
        instantiated = z3.substitute_vars(axiom_body, *args)
        instantiated_axioms.append(instantiated)
    
    # Combine the original formula with all instantiated axioms
    if instantiated_axioms:
        return z3.And(formula, *instantiated_axioms)
    else:
        return formula


def purify(formula: z3.ExprRef) -> z3.ExprRef:
    """
    In Nelson-Oppen method to solving SMT formulas in a combined theory (e.g., linear integer arithmetic and uninterpreted functions), 
    we need to "purify" a formula: purify literals so that each belongs to a single theory.
    
    This function transforms a formula by introducing fresh variables for shared terms between theories,
    resulting in a formula where each atom belongs to a single theory.
    
    Note: This implementation rejects quantified formulas with an exception.
    
    Args:
        formula: Z3 expression to purify
        
    Returns:
        Purified Z3 expression
        
    Raises:
        ValueError: If the formula contains quantifiers
    
    Reference:
        https://web.stanford.edu/class/cs357/lecture11.pdf
    """
    # Check if the formula contains quantifiers
    def contains_quantifier(expr, seen=None):
        if seen is None:
            seen = {}
        if expr in seen:
            return seen[expr]
        if z3.is_quantifier(expr):
            seen[expr] = True
            return True
        if z3.is_app(expr):
            for i in range(expr.num_args()):
                if contains_quantifier(expr.arg(i), seen):
                    seen[expr] = True
                    return True
        seen[expr] = False
        return False
    
    # Reject quantified formulas
    if contains_quantifier(formula):
        raise ValueError("Quantified formulas are not supported by the purify function")
    
    # Dictionary to store already processed subexpressions
    processed = {}
    # Dictionary to store fresh variables for mixed theory terms
    fresh_vars = {}
    # List to store additional equalities for fresh variables
    equalities = []
    
    def is_uf_term(expr):
        """Check if expression is an uninterpreted function application"""
        return z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
    
    def is_arithmetic_term(expr):
        """Check if expression belongs to arithmetic theory"""
        if z3.is_int(expr) or z3.is_real(expr):
            return True
        if z3.is_const(expr) and (expr.sort() == z3.IntSort() or expr.sort() == z3.RealSort()):
            return True
        if z3.is_app(expr):
            # Check for arithmetic operations
            kind = expr.decl().kind()
            arithmetic_ops = [
                z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_MUL, z3.Z3_OP_DIV, 
                z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM, z3.Z3_OP_POWER,
                z3.Z3_OP_LT, z3.Z3_OP_LE, z3.Z3_OP_GT, z3.Z3_OP_GE
            ]
            return kind in arithmetic_ops
        return False
    
    def is_mixed_term(expr):
        """Check if expression contains terms from different theories"""
        if z3.is_const(expr) or z3.is_var(expr):
            return False
        
        if z3.is_app(expr):
            # For comparison operators, check if operands are from different theories
            if expr.decl().kind() in [z3.Z3_OP_EQ, z3.Z3_OP_LT, z3.Z3_OP_LE, z3.Z3_OP_GT, z3.Z3_OP_GE]:
                if expr.num_args() == 2:
                    left = expr.arg(0)
                    right = expr.arg(1)
                    if (is_arithmetic_term(left) and is_uf_term(right)) or \
                       (is_uf_term(left) and is_arithmetic_term(right)):
                        return True
            
            # Check if this is a pure arithmetic or UF term with children from different theories
            if is_arithmetic_term(expr):
                for i in range(expr.num_args()):
                    if is_uf_term(expr.arg(i)) or is_mixed_term(expr.arg(i)):
                        return True
            elif is_uf_term(expr):
                for i in range(expr.num_args()):
                    if is_arithmetic_term(expr.arg(i)) or is_mixed_term(expr.arg(i)):
                        return True
            else:
                # For other operators, check if any child is mixed
                for i in range(expr.num_args()):
                    if is_mixed_term(expr.arg(i)):
                        return True
        
        return False
    
    def purify_term(expr):
        """Purify a term by introducing fresh variables for mixed subterms"""
        if expr in processed:
            return processed[expr]
        
        # Base cases
        if z3.is_const(expr) or z3.is_var(expr):
            processed[expr] = expr
            return expr
        
        # Handle mixed terms
        if is_mixed_term(expr):
            if expr in fresh_vars:
                return fresh_vars[expr]
            
            # Create a fresh variable of the same sort
            fresh_var = z3.Const(f"purify_{len(fresh_vars)}", expr.sort())
            fresh_vars[expr] = fresh_var
            
            # Purify the children first
            purified_expr = expr
            if z3.is_app(expr):
                args = [purify_term(expr.arg(i)) for i in range(expr.num_args())]
                purified_expr = expr.decl()(*args)
            
            # Add equality constraint
            equalities.append(fresh_var == purified_expr)
            processed[expr] = fresh_var
            return fresh_var
        
        # Recursive case for applications
        if z3.is_app(expr):
            args = [purify_term(expr.arg(i)) for i in range(expr.num_args())]
            result = expr.decl()(*args)
            processed[expr] = result
            return result
        
        # Default case
        processed[expr] = expr
        return expr
    
    # Purify the formula
    purified_formula = purify_term(formula)
    
    # Combine the purified formula with the introduced equalities
    if equalities:
        return z3.And(purified_formula, *equalities)
    else:
        return purified_formula


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
    print(replace_func_with_template(chc, inv, template))


def test_instiatiate():
    """
    Example of instantiating an uninterpreted function with an axiom.
    """
    x, y = z3.Ints('x y')
    f = z3.Function('f', z3.IntSort(), z3.IntSort(), z3.BoolSort())
    axiom = z3.ForAll([x, y], z3.Implies(f(x, y), x + y > 0))
    # Create a more complex formula with nested function applications and additional constraints
    a, b, c = z3.Ints('a b c')
    formula = z3.And(
        f(x, y),                  # Basic function application
        f(y, x),                  # Symmetric application
        z3.Implies(f(a, b), f(b, c)),  # Implication with function
        z3.Or(f(x + 1, y - 1), f(x * 2, y / 2)),  # Function with expressions, using / for Z3 integer division
        z3.Not(f(0, 0))           # Negated function application
    )
    print(instiatiate_func_with_axioms(formula, f, axiom))


def test_purify():
    """
    Example of purifying a formula with mixed theories (arithmetic and uninterpreted functions).
    """
    # Create variables and uninterpreted function
    x, y, z = z3.Ints('x y z')
    f = z3.Function('f', z3.IntSort(), z3.IntSort())
    
    # Create a formula with mixed theories
    # f(x + y) > z is a mixed formula because f is UF and (x + y) is arithmetic
    mixed_formula = z3.And(
        f(x + y) > z,
        f(x) + f(y) == 10,
        z > 0
    )
    
    print("Original mixed formula:")
    print(mixed_formula)
    
    # Purify the formula
    purified = purify(mixed_formula)
    
    print("\nPurified formula:")
    print(purified)
    
    # Demonstrate that the formulas are equisatisfiable
    s1 = z3.Solver()
    s1.add(mixed_formula)
    r1 = s1.check()
    
    s2 = z3.Solver()
    s2.add(purified)
    r2 = s2.check()
    
    print("\nOriginal formula satisfiability:", r1)
    print("Purified formula satisfiability:", r2)
    
    if r1 == r2 == z3.sat:
        m1 = s1.model()
        m2 = s2.model()
        print("\nOriginal model:", m1)
        print("Purified model:", m2)
    
    # Test with quantifiers
    print("\n--- Testing with quantifiers ---")
    a, b = z3.Ints('a b')
    g = z3.Function('g', z3.IntSort(), z3.IntSort(), z3.IntSort())
    
    # Formula with quantifiers and mixed theories
    # g(a + b, a - b) > g(a, b) has mixed terms: a+b and a-b in UF application
    quantified_formula = z3.ForAll([a, b], 
                                  z3.Implies(a > b, 
                                            g(a + b, a - b) > g(a, b)))
    
    print("\nOriginal quantified formula:")
    print(quantified_formula)
    
    # Try to purify the quantified formula - should raise an exception
    try:
        purified_quantified = purify(quantified_formula)
        print("\nPurified quantified formula:")
        print(purified_quantified)
    except ValueError as e:
        print(f"\nError: {e}")
        print("As expected, quantified formulas are rejected by the purify function.")


if __name__ == "__main__":
    test_replace()
    print("-" * 100)
    test_instiatiate()
    print("-" * 100)
    test_purify()