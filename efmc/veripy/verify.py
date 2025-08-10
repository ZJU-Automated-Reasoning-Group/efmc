import ast
import z3
import inspect
from typing import List, Tuple, TypeVar
from efmc.veripy.parser.syntax import *
from efmc.veripy.parser.parser import parse_assertion, parse_expr
from functools import wraps
from efmc.veripy.transformer import *
from functools import reduce
from efmc.veripy.prettyprint import pretty_print
from efmc.veripy import typecheck as tc
from efmc.veripy.typecheck.types import TARR, TINT, TBOOL

class VerificationStore:
    def __init__(self):
        self.store = dict()
        self.scope = []
        self.switch = False
        self.pre_states = dict()  # scope -> func_name -> dict(var->z3 const)
        self.func_attrs_global = dict()  # fname -> attrs (inputs, requires, ensures, returns)
    
    def enable_verification(self):
        self.switch = True

    def push(self, scope):
        assert scope not in self.store
        self.scope.append(scope)
        self.store[scope] = {
            'func_attrs' : dict(),
            'vf'         : []
        }
    
    def current_scope(self):
        if self.scope:
            return self.scope[-1]
    
    def push_verification(self, func_name, verification_func):
        if self.switch:
            if not self.scope:
                raise Exception('No Scope Defined')
            self.store[self.scope[-1]]['vf'].append((func_name, verification_func))
    
    def verify(self, scope, ignore_err):
        if self.switch and self.store:
            print(f'=> Verifying Scope `{scope}`')
            verifications = self.store[scope]
            for f_name, f in verifications['vf']:
                try:
                    f()
                except Exception as e:
                    print(f'Exception encountered while verifying {scope}::{f_name}')
                    if not ignore_err:
                        raise e
                    else:
                        print(e)
            print(f'=> End Of `{scope}`\n')
    
    def verify_all(self, ignore_err):
        if self.switch:
            try:
                while self.scope:
                    self.verify(self.scope.pop(), ignore_err)
            except Exception as e:
                if not ignore_err:
                    raise e
                else:
                    print(e)           
    
    def insert_func_attr(self, scope, fname, inputs=[], inputs_map={}, returns=tc.types.TANY, requires=[], ensures=[]):
        if self.switch and self.store:
            self.store[scope]['func_attrs'][fname] = {
                'inputs' : inputs_map,
                'ensures': ensures,
                'requires': requires,
                'returns' : returns,
                'func_type' : tc.types.TARROW(tc.types.TPROD(lambda i: i[1], inputs), returns)
            }
            # Also register globally for summary lookup across scopes
            self.func_attrs_global[fname] = self.store[scope]['func_attrs'][fname]
    
    def get_func_attr(self, fname):
        if self.store:
            # Legacy API: look up in current scope if available
            if self.scope:
                return self.store[self.scope[-1]].get('func_attrs', dict()).get(fname)
            return None
        return None

    def current_func_attrs(self):
        if self.scope:
            return self.store[self.scope[-1]]['func_attrs']
    
    def get_func_attrs(self, scope, fname):
        # Lookup independent of current scope stack (use provided scope key)
        return self.store[scope]['func_attrs'][fname]

STORE = VerificationStore()

def enable_verification():
    STORE.enable_verification()

def scope(name : str):
    STORE.push(name)

def do_verification(name : str, ignore_err : bool=True):
    STORE.verify(name, ignore_err)

def verify_all(ignore_err : bool=True):
    STORE.verify_all(ignore_err)

def invariant(inv):
    return parse_assertion(inv)

def assume(C):
    if not C:
        raise RuntimeError('Assumption Violation')

def wp_seq(sigma, stmt, Q):
    (p2, c2) = wp(sigma, stmt.s2, Q)
    (p1, c1) = wp(sigma, stmt.s1, p2)
    return (p1, c1.union(c2))

def wp_if(sigma, stmt, Q):
    (p1, c1) = wp(sigma, stmt.lb, Q)
    (p2, c2) = wp(sigma, stmt.rb, Q)
    return (
        BinOp(
            BinOp(stmt.cond, BoolOps.Implies, p1),
            BoolOps.And,
            BinOp(
                UnOp(BoolOps.Not, stmt.cond), BoolOps.Implies, p2
            )
        ),
        c1.union(c2)
    )

def wp_while(sigma, stmt: While, Q):
    cond = stmt.cond
    s = stmt.body
    invars = stmt.invariants
    combined_invars = Literal (VBool (True)) if not invars \
                      else reduce(lambda i1, i2: BinOp(i1, BoolOps.And, i2), invars)
    (p, c) = wp(sigma, s, combined_invars)
    # Optional termination side condition: not yet, but place holder here
    return (combined_invars, c.union({
        BinOp(BinOp(combined_invars, BoolOps.And, cond), BoolOps.Implies, p),
        BinOp(BinOp(combined_invars, BoolOps.And, (UnOp(BoolOps.Not, cond))), BoolOps.Implies, Q)
    }))

def wp(sigma, stmt, Q):
    def substitute_many(expr: Expr, mapping: dict):
        result = expr
        for k, v in mapping.items():
            result = subst(k, v, result)
        return result

    def wp_assign_x(stmt: Assign, Q):
        if isinstance(stmt.expr, FunctionCall) and isinstance(stmt.expr.func_name, Var):
            # best-effort summary: assume callee requires holds; conjoin ensures with ans mapped to LHS
            fname = stmt.expr.func_name.name
            # CURRENT_FUNC_ATTRS is set in verify_func; if absent, fallback to normal assign
            attrs = STORE.func_attrs_global.get(fname)
            if attrs is None:
                return (subst(stmt.var, stmt.expr, Q), set())
            param_names = list(attrs['inputs'].keys())
            arg_exprs = stmt.expr.args
            mapping = { pn: ae for pn, ae in zip(param_names, arg_exprs) }
            reqs = attrs.get('requires', [])
            reqs_parsed = [ parse_assertion(r) for r in reqs ]
            req_fold = fold_constraints([ substitute_many(rp, mapping) for rp in reqs_parsed ])
            ens = attrs.get('ensures', [])
            ens_parsed = [ parse_assertion(e) for e in ens ]
            mapping_with_result = dict(mapping)
            mapping_with_result['ans'] = Var(stmt.var) if isinstance(stmt.var, str) else stmt.var
            ens_fold = fold_constraints([ substitute_many(ep, mapping_with_result) for ep in ens_parsed ])
            new_Q = substitute_many(Q, { stmt.var: stmt.expr }) if isinstance(stmt.var, str) else Q
            new_Q = BinOp(new_Q, BoolOps.And, ens_fold)
            return (new_Q, { req_fold })
        return (subst(stmt.var, stmt.expr, Q), set())

    return {
        Skip:   lambda: (Q, set()),
        Assume:  lambda: (BinOp(stmt.e, BoolOps.Implies, Q), set()),
        Assign: lambda: wp_assign_x(stmt, Q),
        Assert: lambda: (BinOp(Q, BoolOps.And, stmt.e), set()),
        Seq:    lambda: wp_seq(sigma, stmt, Q),
        If:     lambda: wp_if(sigma, stmt, Q),
        While:  lambda: wp_while(sigma, stmt, Q),
        Havoc:  lambda: (Quantification(Var(stmt.var + '$0'), subst(stmt.var, Var(stmt.var + '$0'), Q), ty=sigma[stmt.var]), set())
    }.get(type(stmt), lambda: raise_exception(f'wp not implemented for {type(stmt)}'))()

def emit_smt(translator: Expr2Z3, solver, constraint : Expr, fail_msg : str):
    solver.push()
    const = translator.visit(UnOp(BoolOps.Not, constraint))
    solver.add(const)
    if str(solver.check()) == 'sat':
        model = solver.model()
        raise Exception(f'VerificationViolated on\n{const}\nModel: {model}\n{fail_msg}')
    solver.pop()

def fold_constraints(constraints : List[str]):
    fold_and_str = lambda x, y: BinOp(parse_assertion(x) if isinstance(x, str) else x,
                                BoolOps.And, parse_assertion(y) if isinstance(y, str) else y)
    if len(constraints) >= 2:
        return reduce(fold_and_str, constraints)
    elif len(constraints) == 1:
        return parse_assertion(constraints[0])
    else:
        return Literal(VBool(True))

def verify_func(func, scope, inputs, requires, ensures, modifies=None, reads=None):
    code = inspect.getsource(func)
    func_ast = ast.parse(code)
    target_language_ast = StmtTranslator().visit(func_ast)
    func_attrs = STORE.get_func_attrs(scope, func.__name__)
    scope_funcs = STORE.store[scope]['func_attrs']
    sigma = tc.type_check_stmt(func_attrs['inputs'], scope_funcs, target_language_ast)

    user_precond = fold_constraints(requires)
    user_postcond = fold_constraints(ensures)

    tc.type_check_expr(sigma, scope_funcs, TBOOL, user_precond)
    # Allow 'ans' in postconditions with function return type
    sigma_with_ans = dict(sigma)
    sigma_with_ans['ans'] = func_attrs['returns']
    tc.type_check_expr(sigma_with_ans, scope_funcs, TBOOL, user_postcond)

    # Static frame checks if provided
    if modifies is not None and len(modifies) > 0:
        assigned = collect_assigned_vars(target_language_ast)
        illegal = assigned.difference(set(modifies))
        if illegal:
            raise Exception(f'Frame violation: assigns {illegal} not in modifies {set(modifies)}')
    if reads is not None and len(reads) > 0:
        referenced = target_language_ast.variables()
        assigned = collect_assigned_vars(target_language_ast)
        read_vars = referenced.difference(assigned)
        illegal_reads = read_vars.difference(set(reads))
        if illegal_reads:
            raise Exception(f'Reads violation: reads {illegal_reads} not in declared reads {set(reads)}')

    (P, C) = wp(sigma, target_language_ast, user_postcond)
    check_P = BinOp(user_precond, BoolOps.Implies, P)

    solver = z3.Solver()
    current_consts = declare_consts(sigma)
    # Declare logical result 'ans' for use in postconditions
    ret_ty = func_attrs['returns']
    if ret_ty == tc.types.TINT:
        current_consts['ans'] = z3.Int('ans')
    elif ret_ty == tc.types.TBOOL:
        current_consts['ans'] = z3.Bool('ans')
    elif isinstance(ret_ty, tc.types.TARR):
        # array of ints for now
        current_consts['ans'] = z3.Array('ans', z3.IntSort(), z3.IntSort())
    # Build old-state symbols and equate them to current at entry
    def sort_for(ty):
        if ty == tc.types.TINT:
            return z3.IntSort()
        if ty == tc.types.TBOOL:
            return z3.BoolSort()
        if isinstance(ty, tc.types.TARR):
            return z3.ArraySort(z3.IntSort(), sort_for(ty.ty))
        return z3.IntSort()

    def make_old_const(name, ty):
        if ty == tc.types.TINT:
            return z3.Int(name + '$old')
        if ty == tc.types.TBOOL:
            return z3.Bool(name + '$old')
        if isinstance(ty, tc.types.TARR):
            return z3.Array(name + '$old', z3.IntSort(), sort_for(ty.ty))
        # default to int
        return z3.Int(name + '$old')
    old_consts = { name + '$old': make_old_const(name, ty)
                   for name, ty in sigma.items() if type(ty) != dict }
    for name, const in current_consts.items():
        if name + '$old' in old_consts:
            solver.add(old_consts[name + '$old'] == const)

    # Provide function return type map to translator
    fn_ret_types = { n: a['returns'] for n, a in scope_funcs.items() }
    translator = Expr2Z3(current_consts, old_consts, fn_ret_types)

    emit_smt(translator, solver, check_P, f'Precondition does not imply wp at {func.__name__}')
    for c in C:
        emit_smt(translator, solver, c, f'Side condition violated at {func.__name__}')
    print(f'{func.__name__} Verified!')


def declare_consts(sigma : dict):
    consts = dict()
    def sort_for(ty):
        if ty == tc.types.TINT:
            return z3.IntSort()
        if ty == tc.types.TBOOL:
            return z3.BoolSort()
        if isinstance(ty, tc.types.TARR):
            return z3.ArraySort(z3.IntSort(), sort_for(ty.ty))
        # default to int
        return z3.IntSort()
    for (name, ty) in sigma.items():
        if type(ty) != dict:
            if ty == tc.types.TINT:
                consts[name] = z3.Int(name)
            elif ty == tc.types.TBOOL:
                consts[name] = z3.Bool(name)
            elif isinstance(ty, tc.types.TARR):
                consts[name] = z3.Array(name, z3.IntSort(), sort_for(ty.ty))
            else:
                consts[name] = z3.Int(name)
    return consts

def parse_func_types(func, inputs=[]):
    code = inspect.getsource(func)
    func_ast = ast.parse(code)
    func_def = func_ast.body[0]
    result = []
    provided = dict(inputs)
    for i in func_def.args.args:
        if i.annotation:
            result.append(tc.types.to_ast_type(i.annotation))
        else:
            result.append(provided.get(i.arg, tc.types.TANY))
        provided[i.arg] = result[-1]

    if func_def.returns:
        ret_type = tc.types.to_ast_type(func_def.returns)
        return (result, provided, ret_type)
    else:
        raise Exception('Return annotation is required for verifying functions')

def verify(inputs: List[Tuple[str, tc.types.SUPPORTED]]=[], requires: List[str]=[], ensures: List[str]=[], modifies: List[str]=[], reads: List[str]=[], decreases: str=None):
    def verify_impl(func):
        @wraps(func)
        def caller(*args, **kargs):
            return func(*args, **kargs)
        types = parse_func_types(func, inputs=inputs)
        scope = STORE.current_scope()
        STORE.insert_func_attr(scope, func.__name__, types[0], types[1], types[2], requires, ensures)
        STORE.push_verification(func.__name__, lambda: verify_func(func, scope, inputs, requires, ensures, modifies, reads))
        return caller
    return verify_impl

def collect_assigned_vars(stmt: Stmt) -> set:
    if isinstance(stmt, Skip):
        return set()
    if isinstance(stmt, Assign):
        return {stmt.var} if isinstance(stmt.var, str) else set()
    if isinstance(stmt, Seq):
        return collect_assigned_vars(stmt.s1).union(collect_assigned_vars(stmt.s2))
    if isinstance(stmt, If):
        return collect_assigned_vars(stmt.lb).union(collect_assigned_vars(stmt.rb))
    if isinstance(stmt, While):
        return collect_assigned_vars(stmt.body)
    if isinstance(stmt, Havoc):
        return {stmt.var}
    return set()