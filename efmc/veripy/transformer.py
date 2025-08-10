import ast
import z3
from efmc.veripy.parser.syntax import *
from efmc.veripy.parser.parser import parse_assertion
from efmc.veripy.built_ins import BUILT_INS, FUNCTIONS
from efmc.veripy.typecheck.types import *
from functools import reduce
from typing import List

def raise_exception(msg : str):
    raise Exception(msg)

def subst(this : str, withThis : Expr, inThis : Expr) -> Expr:
    '''
    Substitute a variable (`this`) with `withThis` in expression `inThis` and return the resulted expression
    '''
    if isinstance(inThis, Var):
        if inThis.name == this:
            return withThis
        else:
            return inThis
    if isinstance(inThis, BinOp):
        return BinOp(subst(this, withThis, inThis.e1), inThis.op, subst(this, withThis, inThis.e2))
    if isinstance(inThis, Literal):
        return inThis
    if isinstance(inThis, UnOp):
        return UnOp(inThis.op, subst(this, withThis, inThis.e))
    if isinstance(inThis, Quantification):
        if this != inThis.var:
            return Quantification(inThis.var, subst(this, withThis, inThis.expr), inThis.ty)
        return inThis
    if isinstance(inThis, FunctionCall):
        return inThis
    if isinstance(inThis, Subscript):
        return Subscript(
            subst(this, withThis, inThis.var),
            subst(this, withThis, inThis.subscript)
        )
    if isinstance(inThis, Store):
        return Store(
            subst(this, withThis, inThis.arr),
            subst(this, withThis, inThis.idx),
            subst(this, withThis, inThis.val)
        )
    if isinstance(inThis, Old):
        # Do not substitute under Old; it refers to pre-state
        return inThis
    
    raise NotImplementedError(f'Substitution not implemented for {type(inThis)}')

class ExprTranslator:
    '''
    Translator that can convert a Python expression AST to veripy AST
    '''
    def fold_binops(self, op : Op, values : List[Expr]):
        result = BinOp(self.visit(values[0]), op, self.visit(values[1]))
        for e in values[2:]:
            result = BinOp(result, op, self.visit(e))
        return result

    def visit_Name(self, node):
        return Var(node.id)
    
    def visit_Num(self, node):
        return Literal (VInt (node.n))
    
    def visit_NameConstant(self, node):
        return Literal (VBool (node.value))

    def visit_Expr(self, node):
        return self.visit(node.value)
    
    def visit_BoolOp(self, node):
        op = {
                ast.And:    BoolOps.And,
                ast.Or:     BoolOps.Or,
             }.get(type(node.op))
        return self.fold_binops(op, node.values)
    
    def visit_Compare(self, node):
        '''
        Do not support multiple comparators
        because the expansion will cause inconsistent interpretation if
        parsed using PEP standard.
        Consider `1 in (1, 2) == True`.
        '''
        lv = self.visit(node.left)
        rv = self.visit(node.comparators[0])
        op = node.ops[0]
        return {
            ast.Lt:     lambda: BinOp(lv, CompOps.Lt, rv),
            ast.LtE:    lambda: BinOp(lv, CompOps.Le, rv),
            ast.Gt:     lambda: BinOp(lv, CompOps.Gt, rv),
            ast.GtE:    lambda: BinOp(lv, CompOps.Ge, rv),
            ast.Eq:     lambda: BinOp(lv, CompOps.Eq, rv),
            ast.NotEq:  lambda: BinOp(lv, CompOps.Neq, rv),
        }.get(type(op), lambda: raise_exception(f'Not Supported: {op}'))()

    def visit_BinOp(self, node):
        lv = self.visit(node.left)
        rv = self.visit(node.right)
        return {
            ast.Add:    lambda: BinOp(lv, ArithOps.Add, rv),
            ast.Sub:    lambda: BinOp(lv, ArithOps.Minus, rv),
            ast.Mult:   lambda: BinOp(lv, ArithOps.Mult, rv),
            ast.Div:    lambda: BinOp(lv, ArithOps.IntDiv, rv),
            ast.Mod:    lambda: BinOp(lv, ArithOps.Mod, rv)
        }.get(type(node.op), lambda: raise_exception(f'Not Supported: {node.op}'))()
    
    def visit_UnaryOp(self, node):
        v = self.visit(node.operand)
        return {
            ast.USub:   lambda: UnOp(ArithOps.Neg, v),
            ast.Not:    lambda: UnOp(BoolOps.Not, v)
        }.get(type(node.op), lambda: raise_exception(f'Not Supported {node.op}'))()

    def visit_Index(self, node):
        return self.visit(node.value)
    
    def visit_Call(self, node):
        # Support Name and Attribute (e.g., vp.invariant)
        func = node.func.id if isinstance(node.func, ast.Name) else (
            node.func.attr if isinstance(node.func, ast.Attribute) else None
        )
        if func in BUILT_INS:
            if func == 'assume':
                return Assume(parse_assertion(node.args[0].s))
            if func == 'invariant':
                return parse_assertion(node.args[0].s)
        else:
            if func is None:
                raise_exception(f'Unsupported call func: {ast.dump(node.func)}')
            return FunctionCall(Var(func), list(map(lambda x: Var(x.id), node.args)))
    
    def visit_Slice(self, node):
        lo, hi, step = [None] * 3
        if node.lower:
            lo = self.visit(node.lower)
        if node.upper:
            hi = self.visit(node.upper)
        if node.step:
            step = self.visit(node.step)
        
        return Slice(lo, hi, step)

    def visit_Subscript(self, node):
        v = self.visit(node.value)
        return Subscript(v, self.visit(node.slice))

    def visit_Attribute(self, node):
        # Treat obj.field as a record field for specs; verification will be shallow unless modeled
        obj = self.visit(node.value)
        return RecordField(obj, node.attr)

    def visit_Constant(self, node):
        assert isinstance(node, ast.Constant)
        value = node.value
        if isinstance(value, bool):
            return Literal (VBool (value))
        if isinstance(value, int):
            return Literal (VInt (value))
        raise_exception(f'Unsupported constant: {value}')

    def visit_Dict(self, node):
        # Map to an empty record placeholder; no concrete semantics
        return Literal(VInt(0))

    def visit_Set(self, node):
        return Literal(VInt(0))
    
    def visit(self, node):
        # if isinstance(node, ast.Constant):
        #     print(dir(node), node.s, node.n, node.value)
        return {
                ast.BinOp:          lambda: self.visit_BinOp(node),
                ast.Name:           lambda: self.visit_Name(node),
                ast.Compare:        lambda: self.visit_Compare(node),
                ast.BoolOp:         lambda: self.visit_BoolOp(node),
                ast.NameConstant:   lambda: self.visit_NameConstant(node),
                ast.Num:            lambda: self.visit_Num(node),
                ast.UnaryOp:        lambda: self.visit_UnaryOp(node),
                ast.Call:           lambda: self.visit_Call(node),
                ast.Subscript:      lambda: self.visit_Subscript(node),
                ast.Attribute:      lambda: self.visit_Attribute(node),
                ast.Index:          lambda: self.visit_Index(node),
                ast.Constant:       lambda: self.visit_Constant(node),
                ast.Dict:           lambda: self.visit_Dict(node),
                ast.Set:            lambda: self.visit_Set(node),
            }.get(type(node), lambda: raise_exception(f'Expr not supported: {node}'))()

class StmtTranslator:
    '''
    Translator that can convert a Python statement AST to veripy AST
    '''
    def __init__(self):
        self.expr_translator = ExprTranslator()

    def make_seq(self, stmts, need_visit=True):
        '''
        Fold a list of statements to `Seq` node.
        Argument:
            - stmts         : the list of statements to fold
            - need_visit    : each node in `stmts` will be first visited before filling into `Seq` if
                              `need_visit` is True; otherwise, each node will be filled in directly.
        '''
        if stmts:
            hd, *stmts = stmts
            t_node = self.visit(hd) if need_visit else hd
            while stmts:
                t2_node, stmts = self.visit(stmts[0]) if need_visit else stmts[0], stmts[1:]
                t_node = Seq(t_node, t2_node)
            if not isinstance(t_node, Seq):
                return Seq(t_node, Skip())
            return t_node
        else:
            return Skip()
    
    def visit_Call(self, node):
        func = node.func.id if isinstance(node.func, ast.Name) else (
            node.func.attr if isinstance(node.func, ast.Attribute) else None
        )
        if func in BUILT_INS:
            if func == 'assume':
                return Assume(parse_assertion(node.args[0].s))
            if func == 'invariant':
                return parse_assertion(node.args[0].s)
        else:
            if func is None:
                raise_exception(f'Unsupported call func: {ast.dump(node.func)}')
            return FunctionCall(Var(func), list(map(lambda x: Var(x.id), node.args)))
    
    def visit_FunctionDef(self, node):
        return self.make_seq(node.body)
    
    def visit_Module(self, node):
        return self.make_seq(node.body)
    
    def visit_Return(self, node):
        return Skip()

    def visit_Assign(self, node):
        target = node.targets[0]
        expr = self.expr_translator.visit(node.value)
        # Array element assignment becomes a functional array store
        if isinstance(target, ast.Subscript):
            arr = self.expr_translator.visit(target.value)
            idx = self.expr_translator.visit(target.slice)
            # We require the base to be a variable name for assignment target bookkeeping
            if isinstance(arr, Var):
                varname = arr.name
            else:
                raise_exception(f'Assignment target not supported: {ast.dump(target)}')
            return Assign(varname, Store(arr, idx, expr))
        else:
            varname = target.id
            return Assign(varname, expr)

    def visit_For(self, node):
        # Support `for i in range(start, stop, step?)` as while with explicit variant
        # Only handle range(...) forms
        if not isinstance(node.iter, ast.Call):
            raise_exception('Only for ... in range(...) is supported')
        if isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range':
            args = node.iter.args
            if len(args) == 1:
                start = Literal(VInt(0))
                stop = self.expr_translator.visit(args[0])
                step = Literal(VInt(1))
            elif len(args) == 2:
                start = self.expr_translator.visit(args[0])
                stop = self.expr_translator.visit(args[1])
                step = Literal(VInt(1))
            elif len(args) == 3:
                start = self.expr_translator.visit(args[0])
                stop = self.expr_translator.visit(args[1])
                step = self.expr_translator.visit(args[2])
            else:
                raise_exception('range() with 1..3 args expected')

            # Initialization: i = start
            assert isinstance(node.target, ast.Name)
            ivar = node.target.id
            init = Assign(ivar, start)
            # Loop: while i < stop: invariants; body; i = i + step
            cond = BinOp(Var(ivar), CompOps.Lt, stop)
            def is_invariant(y):
                if not (isinstance(y, ast.Expr) and isinstance(y.value, ast.Call)):
                    return False
                f = y.value.func
                if isinstance(f, ast.Name):
                    return f.id == 'invariant'
                if isinstance(f, ast.Attribute):
                    return f.attr == 'invariant'
                return False
            invariant_stmts = list(filter(is_invariant, node.body))
            invars = [self.visit_Call(x.value) for x in invariant_stmts]
            def not_invariant_stmt(x):
                if isinstance(x, ast.Expr) and isinstance(x.value, ast.Call):
                    f = x.value.func
                    if isinstance(f, ast.Name):
                        return f.id != 'invariant'
                    if isinstance(f, ast.Attribute):
                        return f.attr != 'invariant'
                return True
            body_seq = self.make_seq(list(filter(not_invariant_stmt, node.body)))
            inc = Assign(ivar, BinOp(Var(ivar), ArithOps.Add, step))
            loop_body = self.make_seq([body_seq, inc], need_visit=False)
            w = self.make_seq([While(invars, cond, loop_body)], need_visit=False)
            return self.make_seq([init, w], need_visit=False)
        else:
            raise_exception('Only range() iterables supported in for-loops')

    def visit_While(self, node):
        '''
        Visit the while statement. The conversion rule is:
            While e S
            ==>
            assert invariant
            havoc x (for all x referred in S)
            assume invariant
            if e then S;assert invariants;assume false
            else skip
        '''
        cond = self.expr_translator.visit(node.test)
        def is_invariant(y):
            if not (isinstance(y, ast.Expr) and isinstance(y.value, ast.Call)):
                return False
            f = y.value.func
            if isinstance(f, ast.Name):
                return f.id == 'invariant'
            if isinstance(f, ast.Attribute):
                return f.attr == 'invariant'
            return False
        # Since invariants are specified using a dummy function call, here we can use this directly
        invariant_stmts = list(filter(is_invariant, node.body))
        invars = [self.visit_Call(x.value) for x in invariant_stmts]
        # Filter out invariant expressions from the loop body
        def not_invariant_stmt(x):
            if isinstance(x, ast.Expr) and isinstance(x.value, ast.Call):
                f = x.value.func
                if isinstance(f, ast.Name):
                    return f.id != 'invariant'
                if isinstance(f, ast.Attribute):
                    return f.attr != 'invariant'
            return True
        body = self.make_seq(list(filter(not_invariant_stmt, node.body)))
        loop_targets = body.variables()
        havocs = list(map(Havoc, loop_targets))
        invariants = Literal (VBool (True)) if not invars \
                      else reduce(lambda i1, i2: BinOp(i1, BoolOps.And, i2), invars)
        return self.make_seq(
            [   Assert(invariants),
                *havocs,
                Assume(invariants),
                If(cond,
                    self.make_seq(
                        [   body,
                            Assert(invariants),
                            Assume(Literal(VBool(False)))
                        ], need_visit=False),
                    Skip())
            ]
        , need_visit=False)
    
    def visit_If(self, node):
        cond = self.expr_translator.visit(node.test)
        lb = self.make_seq(node.body)
        rb = self.make_seq(node.orelse)
        return If(cond, lb, rb)
    
    def visit_Assert(self, node):
        return Assert(self.expr_translator.visit(node.test))
    
    def visit_AnnAssign(self, node):
        # Handle annotated assignments like `x: bool = True`
        if node.value is None:
            # Treat as skip if only a declaration
            return Skip()
        target = node.target
        expr = self.expr_translator.visit(node.value)
        if isinstance(target, ast.Name):
            return Assign(target.id, expr)
        if isinstance(target, ast.Subscript):
            arr = self.expr_translator.visit(target.value)
            idx = self.expr_translator.visit(target.slice)
            if isinstance(arr, Var):
                return Assign(arr.name, Store(arr, idx, expr))
        raise_exception(f'Annotated assignment target not supported: {ast.dump(node)}')
    
    def visit(self, node):
        return {
                ast.FunctionDef: lambda: self.visit_FunctionDef(node),
                ast.Module:      lambda: self.visit_Module(node),
                ast.If:          lambda: self.visit_If(node),
                ast.While:       lambda: self.visit_While(node),
                ast.For:         lambda: self.visit_For(node),
                ast.Assert:      lambda: self.visit_Assert(node),
                ast.Assign:      lambda: self.visit_Assign(node),
                ast.AnnAssign:   lambda: self.visit_AnnAssign(node),
                ast.Return:      lambda: self.visit_Return(node),
                ast.Call:        lambda: self.visit_Call(node),
                ast.Pass:        lambda: Skip()
            }.get(type(node), lambda: raise_exception(f'Stmt not supported: {node}'))()


class Expr2Z3:
    '''
    Translator that translates a veripy expression AST to a Z3 constraint
    '''
    def __init__(self, name_dict: dict, old_dict: dict=None, func_returns: dict=None):
        self.name_dict = name_dict
        self.old_dict = old_dict or {}
        self.func_returns = func_returns or {}
        # Uninterpreted length for integer arrays
        self._len_fun = z3.Function('len_int', z3.ArraySort(z3.IntSort(), z3.IntSort()), z3.IntSort())
        # Uninterpreted cardinality for int sets and domain for int->int maps
        self._card_set_fun = z3.Function('card_set_int', z3.ArraySort(z3.IntSort(), z3.BoolSort()), z3.IntSort())
        self._dom_map_fun = z3.Function('dom_map_int', z3.ArraySort(z3.IntSort(), z3.IntSort()), z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        self._card_set_fun = z3.Function('card_set_int', z3.ArraySort(z3.IntSort(), z3.BoolSort()), z3.IntSort())

    def translate_type(self, ty):
        if ty == TINT:
            return z3.IntSort()
        if ty == TBOOL:
            return z3.BoolSort()
        if isinstance(ty, TARR):
            return z3.ArraySort(z3.IntSort(), self.translate_type(ty.ty))

    def visit_Literal(self, lit : Literal):
        v = lit.value
        return {
            VBool: lambda: v.v,
            VInt: lambda: v.v
        }.get(type(v), lambda: raise_exception(f'Unsupported data: {v}'))()

    def visit_Var(self, node : Var):
        # Interpret Old(x) lowering happens at parser level; variables with $old are looked up in old_dict
        if node.name.endswith('$old'):
            if node.name in self.old_dict:
                return self.old_dict[node.name]
            # Fallback if missing
            return self.name_dict[node.name]
        return self.name_dict[node.name]
    
    def visit_BinOp(self, node : BinOp):
        c1 = self.visit(node.e1)
        c2 = self.visit(node.e2)
        return {
            ArithOps.Add:       lambda: c1 + c2,
            ArithOps.Minus:     lambda: c1 - c2,
            ArithOps.Mult:      lambda: c1 * c2,
            ArithOps.IntDiv:    lambda: c1 / c2,
            ArithOps.Mod:       lambda: c1 % c2,
            
            BoolOps.And:        lambda: z3.And(c1, c2),
            BoolOps.Or:         lambda: z3.Or(c1, c2),
            BoolOps.Implies:    lambda: z3.Implies(c1, c2),
            BoolOps.Iff:        lambda: z3.And(z3.Implies(c1, c2), z3.Implies(c2, c1)),

            CompOps.Eq:         lambda: c1 == c2,
            CompOps.Neq:        lambda: z3.Not(c1 == c2),
            CompOps.Gt:         lambda: c1 > c2,
            CompOps.Ge:         lambda: c1 >= c2,
            CompOps.Lt:         lambda: c1 < c2,
            CompOps.Le:         lambda: c1 <= c2,
            CompOps.In:         lambda: z3.Select(c2, c1)
        }.get(node.op, lambda: raise_exception(f'Unsupported Operator: {node.op}'))()
    
    def visit_UnOp(self, node : UnOp):
        c = self.visit(node.e)
        return {
            ArithOps.Neg: lambda: -c,
            BoolOps.Not:  lambda: z3.Not(c)
        }.get(node.op, lambda: raise_exception(f'Unsupported Operator: {node.op}'))()
    
    def visit_Quantification(self, node : Quantification):
        bound_var = None
        if node.ty == TINT:
            bound_var = z3.Int(node.var.name)
        elif node.ty == TBOOL:
            bound_var = z3.Bool(node.var.name)
        elif isinstance(node.ty, TARR):
            bound_var = z3.Array(z3.IntSort(), self.translate_type(node.ty.ty))
        if bound_var is not None:
            self.name_dict[node.var.name] = bound_var
            return z3.ForAll(bound_var, self.visit(node.expr))
        else:
            raise Exception(f'Unsupported quantified type: {node.ty}')

    def visit_Old(self, node: Old):
        # Translate Old(e) by redirecting variables to their $old versions
        if isinstance(node.expr, Var):
            return self.visit(Var(node.expr.name + '$old'))
        if isinstance(node.expr, Subscript):
            base = node.expr.var
            sub = node.expr.subscript
            if isinstance(base, Var):
                return self.visit(Subscript(Var(base.name + '$old'), sub))
        raise_exception(f'Old not supported for {node.expr}')

    def visit_Subscript(self, node: Subscript):
        arr = self.visit(node.var)
        idx = self.visit(node.subscript)
        return z3.Select(arr, idx)

    def visit_Store(self, node: Store):
        arr = self.visit(node.arr)
        idx = self.visit(node.idx)
        val = self.visit(node.val)
        return z3.Store(arr, idx, val)

    def visit_FunctionCall(self, node: FunctionCall):
        # Currently support len(array)
        if isinstance(node.func_name, Var) and node.func_name.name == 'len':
            assert len(node.args) == 1
            arr = self.visit(node.args[0])
            return self._len_fun(arr)
        if isinstance(node.func_name, Var) and node.func_name.name == 'set':
            # empty int set
            return z3.K(z3.IntSort(), z3.BoolVal(False))
        if isinstance(node.func_name, Var) and node.func_name.name == 'card':
            assert len(node.args) == 1
            s = self.visit(node.args[0])
            return self._card_set_fun(s)
        if isinstance(node.func_name, Var) and node.func_name.name == 'mem':
            assert len(node.args) == 2
            s = self.visit(node.args[0])
            x = self.visit(node.args[1])
            return z3.Select(s, x)
        if isinstance(node.func_name, Var) and node.func_name.name == 'dict':
            # empty int->int map defaulting to 0
            return z3.K(z3.IntSort(), z3.IntVal(0))
        if isinstance(node.func_name, Var) and node.func_name.name == 'keys':
            assert len(node.args) == 1
            m = self.visit(node.args[0])
            return self._dom_map_fun(m)
        # Uninterpreted function application for pure user functions by name
        if isinstance(node.func_name, Var):
            fname = node.func_name.name
            arg_terms = [self.visit(a) for a in node.args]
            # For now, model return sort from declared return type if available
            ret_sort = self.translate_type(self.func_returns.get(fname, TINT))
            uf = z3.Function(f'uf_{fname}', *[z3.IntSort() for _ in arg_terms], ret_sort)
            return uf(*arg_terms)
        raise_exception(f'Unsupported function call: {node}')

    def visit(self, expr : Expr):
        return {
            Literal:            lambda: self.visit_Literal(expr),
            Var:                lambda: self.visit_Var(expr),
            BinOp:              lambda: self.visit_BinOp(expr),
            UnOp:               lambda: self.visit_UnOp(expr),
            Quantification:     lambda: self.visit_Quantification(expr),
            Subscript:          lambda: self.visit_Subscript(expr),
            Store:              lambda: self.visit_Store(expr),
            Old:                lambda: self.visit_Old(expr),
            FunctionCall:       lambda: self.visit_FunctionCall(expr)
        }.get(type(expr), lambda: raise_exception(f'Unsupported AST: {expr}'))()