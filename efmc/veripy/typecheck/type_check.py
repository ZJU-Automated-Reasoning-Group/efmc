from typing import List
from efmc.veripy.parser.syntax import *
from efmc.veripy.typecheck import types as ty
from efmc.veripy.built_ins import FUNCTIONS
from efmc.veripy.log import log

def issubtype(actual, expected):
    # Any accepts anything
    if expected == ty.TANY:
        return True
    # Unknown cannot be assumed to be a subtype of a concrete type
    if actual == ty.TANY:
        return False
    # Exact match
    if actual == expected:
        return True
    # Arrays are covariant in element type for our purposes
    if isinstance(actual, ty.TARR) and isinstance(expected, ty.TARR):
        return issubtype(actual.ty, expected.ty)
    return False

def type_check_stmt(sigma : dict, func_sigma : dict, stmt : Stmt):
    if isinstance(stmt, Skip):
        return sigma
    if isinstance(stmt, Seq):
        return type_check_stmt(type_check_stmt(sigma, func_sigma, stmt.s1), func_sigma, stmt.s2)
    if isinstance(stmt, Assign):
        inferred = type_infer_expr(sigma, func_sigma, stmt.expr)
        # If left-hand side is a name (string), assign or check
        if isinstance(stmt.var, str):
            if stmt.var not in sigma:
                sigma[stmt.var] = inferred
                return sigma
            else:
                if sigma[stmt.var] == ty.TANY:
                    sigma[stmt.var] = inferred
                elif sigma[stmt.var] != inferred:
                    raise TypeError(f'Mutating Type of {stmt.var}!')
                return sigma
        # If left-hand side is an array store, its type must be array
        if isinstance(stmt.expr, Store):
            arr_expr: Expr = stmt.expr.arr
            idx_expr: Expr = stmt.expr.idx
            val_expr: Expr = stmt.expr.val
            arr_ty = type_check_expr(sigma, func_sigma, ty.TANY, arr_expr)
            # Ensure array type
            if not isinstance(arr_ty, ty.TARR):
                # allow late binding: establish as array if unknown
                if isinstance(arr_expr, Var) and sigma.get(arr_expr.name, ty.TANY) == ty.TANY:
                    elem_ty = type_infer_expr(sigma, func_sigma, val_expr)
                    sigma[arr_expr.name] = ty.TARR(elem_ty)
                else:
                    raise TypeError(f'Assignment to subscript requires array type, got {arr_ty}')
            # Index must be int
            type_check_expr(sigma, func_sigma, ty.TINT, idx_expr)
            # Value must match element type
            elem_ty = arr_ty.ty if isinstance(arr_ty, ty.TARR) else type_infer_expr(sigma, func_sigma, val_expr)
            type_check_expr(sigma, func_sigma, elem_ty, val_expr)
            return sigma
    if isinstance(stmt, If):
        type_check_expr(sigma, func_sigma, ty.TBOOL, stmt.cond)
        return type_check_stmt(type_check_stmt(sigma, func_sigma, stmt.lb), func_sigma, stmt.rb)
    if isinstance(stmt, Assert) or isinstance(stmt, Assume):
        type_check_expr(sigma, func_sigma, ty.TBOOL, stmt.e)
        return sigma
    if isinstance(stmt, While):
        type_check_expr(sigma, func_sigma, ty.TBOOL, stmt.cond)
        for i in stmt.invariants:
            type_check_expr(sigma, func_sigma, ty.TBOOL, i)
        return type_check_stmt(sigma, func_sigma, stmt.body)
    if isinstance(stmt, Havoc):
        return sigma
    
    raise NotImplementedError(f'type check not implemented for: {type(stmt)}')

def type_check_expr(sigma: dict, func_sigma : dict, expected, expr: Expr):
    actual = type_infer_expr(sigma, func_sigma, expr)
    if actual == ty.TANY and isinstance(expr, Var):
        sigma[expr.name] = expected
        return expected
    if actual == expected or issubtype(actual, expected):
        return actual
    else:
        raise TypeError(f'{expr}: expected type {expected}, actual type {actual};\
                        issubtype({actual}, {expected})={issubtype(actual, expected)}')

###############################################
#               Type Inference                #
###############################################

def type_infer_Subscript(sigma, func_sigma, expr: Subscript):
    obj = expr.var
    obj_ty = type_infer_expr(sigma, func_sigma, obj)
    # index must be int
    type_check_expr(sigma, func_sigma, ty.TINT, expr.subscript)
    if isinstance(obj_ty, ty.TARR):
        return obj_ty.ty
    # Late binding: if unknown variable, assume it is an array of any, refined by context
    if isinstance(obj, Var) and sigma.get(obj.name, ty.TANY) == ty.TANY:
        sigma[obj.name] = ty.TARR(ty.TANY)
        return ty.TANY
    return ty.TANY

def type_infer_literal(sigma, func_sigma, expr: Literal):
    return {
        VBool: ty.TBOOL,
        VInt : ty.TINT,
    }.get(type(expr.value))

def type_infer_UnOp(sigma, func_sigma, expr: UnOp):
    if expr.op == BoolOps.Not:
        return type_check_expr(sigma, func_sigma, ty.TBOOL, expr.e)
    if expr.op == ArithOps.Neg:
        return type_check_expr(sigma, func_sigma, ty.TINT, expr.e)

def type_infer_BinOp(sigma, func_sigma, expr: BinOp):
    if isinstance(expr.op, ArithOps):
        type_check_expr(sigma, func_sigma, ty.TINT, expr.e1)
        return type_check_expr(sigma, func_sigma, ty.TINT, expr.e2)
    if isinstance(expr.op, CompOps):
        type_check_expr(sigma, func_sigma, ty.TINT, expr.e1)
        type_check_expr(sigma, func_sigma, ty.TINT, expr.e2)
        return ty.TBOOL
    if isinstance(expr.op, BoolOps):
        type_check_expr(sigma, func_sigma, ty.TBOOL, expr.e1)
        return type_check_expr(sigma, func_sigma, ty.TBOOL, expr.e2)

def type_infer_Slice(sigma, func_sigma, expr: Slice):
    if expr.lower or expr.upper or expr.step:
        if expr.lower:
            type_check_expr(sigma, func_sigma, ty.TINT, expr.lower)
        if expr.upper:
            type_check_expr(sigma, func_sigma, ty.TINT, expr.upper)
        if expr.step:
            type_check_expr(sigma, func_sigma, ty.TINT, expr.step)
        return ty.TSLICE
    raise Exception('Slice must have at least one field that is not None')

def type_infer_FunctionCall(sigma, func_sigma: dict, expr: FunctionCall):
    if isinstance(expr.func_name, Var) and expr.func_name.name == 'len':
        if len(expr.args) != 1:
            raise TypeError('len expects exactly one argument')
        # The argument can be an array or sequence; we return int
        return ty.TINT
    if isinstance(expr.func_name, Var):
        fname = expr.func_name.name
        # Use provided function typing env if available
        if fname in func_sigma:
            fty = func_sigma[fname]['returns'] if isinstance(func_sigma[fname], dict) else func_sigma[fname]
            return fty
        # Default to int for unknown
        return ty.TINT
    raise NotImplementedError(f'Function call typing not supported: {expr}')

def type_infer_quantification(sigma, func_sigma, expr: Quantification):
    sigma[expr.var.name] = ty.TANY if expr.ty is None else expr.ty
    type_check_expr(sigma, func_sigma, ty.TBOOL, expr.expr)
    if sigma[expr.var.name] == ty.TANY:
        raise Exception(f'Cannot infer type for {expr.var} in {expr}')
    expr.ty = sigma[expr.var.name]
    sigma.pop(expr.var.name)
    return ty.TBOOL

def type_infer_expr(sigma: dict, func_sigma : dict, expr: Expr):
    if isinstance(expr, Literal):
        return type_infer_literal(sigma, func_sigma, expr)
    if isinstance(expr, Var):
        assert sigma is not None
        assert expr.name in sigma
        return sigma[expr.name]
    if isinstance(expr, UnOp):
        return type_infer_UnOp(sigma, func_sigma, expr)
    if isinstance(expr, BinOp):
        return type_infer_BinOp(sigma, func_sigma, expr)
    if isinstance(expr, Slice):
        return type_infer_Slice(sigma, func_sigma, expr)
    if isinstance(expr, Quantification):
        return type_infer_quantification(sigma, func_sigma, expr)
    if isinstance(expr, Subscript):
        return type_infer_Subscript(sigma, func_sigma, expr)
    if isinstance(expr, Store):
        # store(a, i, v) has type Array(elemTy)
        arr_ty = type_infer_expr(sigma, func_sigma, expr.arr)
        type_check_expr(sigma, func_sigma, ty.TINT, expr.idx)
        val_ty = type_infer_expr(sigma, func_sigma, expr.val)
        if isinstance(arr_ty, ty.TARR):
            type_check_expr(sigma, func_sigma, arr_ty.ty, expr.val)
            return arr_ty
        # If not known, create array type with val_ty
        if isinstance(expr.arr, Var) and sigma.get(expr.arr.name, ty.TANY) == ty.TANY:
            sigma[expr.arr.name] = ty.TARR(val_ty)
            return sigma[expr.arr.name]
        return ty.TARR(val_ty)
    if isinstance(expr, FunctionCall):
        # Built-ins only for now: len, set, dict, card, mem, keys
        if isinstance(expr.func_name, Var) and expr.func_name.name in ('set', 'dict', 'card', 'mem', 'keys'):
            return ty.TANY
        return type_infer_FunctionCall(sigma, func_sigma, expr)
    if isinstance(expr, Old):
        return type_infer_expr(sigma, func_sigma, expr.expr)
    if isinstance(expr, RecordField):
        # Treat fields as ints/bools by default (conservative)
        return ty.TANY

    raise NotImplementedError(f'Unknown expression: {expr}')
