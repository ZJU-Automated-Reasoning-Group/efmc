import typing
import ast

TINT = int
TBOOL = bool
TSLICE = typing.TypeVar('Slice')
TANY = typing.Any

class Type: pass

class TARROW(Type):
    def __init__(self, t1, t2):
        self.t1 = t1
        self.t2 = t2

class TPROD(Type):
    def __init__(self, *types):
        self.types = tuple(types)

class TARR(Type):
    def __init__(self, ty):
        # Array with integer indices and element type ty
        self.ty = ty
    def __repr__(self):
        return f'TARR({self.ty})'

class TSET(Type):
    def __init__(self, elem_ty):
        self.elem_ty = elem_ty
    def __repr__(self):
        return f'TSET({self.elem_ty})'

class TDICT(Type):
    def __init__(self, key_ty, val_ty):
        self.key_ty = key_ty
        self.val_ty = val_ty
    def __repr__(self):
        return f'TDICT({self.key_ty},{self.val_ty})'

def name_to_ast_type(node):
    return {
        'int' : TINT,
        'bool': TBOOL
    }.get(node.id, TANY)

def subscript_to_ast_type(node):
    ty_contr = node.value.id
    if node.slice is None:
        return TANY
    # Handle Python AST differences across versions: slice may have `.value` or be the node itself
    slice_node = getattr(node.slice, 'value', node.slice)
    # Treat typing annotations
    if ty_contr == 'List':
        ty_arg = to_ast_type(slice_node)
        return TARR(ty_arg)
    if ty_contr == 'Set':
        elem_ty = to_ast_type(slice_node)
        return TSET(elem_ty)
    if ty_contr == 'Dict':
        # Expect two type args in a tuple
        if hasattr(slice_node, 'elts') and len(slice_node.elts) == 2:
            k = to_ast_type(slice_node.elts[0])
            v = to_ast_type(slice_node.elts[1])
            return TDICT(k, v)
        return TANY
    if ty_contr == 'Tuple':
        ty_arg = to_ast_type(slice_node)
        return typing.Tuple[ty_arg]
    return TANY

def to_ast_type(ty):
    return {
            ast.Name        : name_to_ast_type,
            ast.Subscript   : subscript_to_ast_type
    }.get(type(ty), lambda _: TANY)(ty)

BUILT_IN_FUNC_TYPE = {
    'len' : TARROW(typing.Sequence[typing.Any], TINT)
}

SUPPORTED = typing.Union[TINT, TBOOL, TARR, TSET, TDICT, typing.List]