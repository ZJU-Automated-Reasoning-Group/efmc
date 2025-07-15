"""
Simplified Template DSL for Invariant Generation

Grammar:
Invariant  ::= Atom | Atom && Atom | ...
Atom       ::= EQ | ULE | ULT | BITMASK | POPCNT | ROT 
EQ         ::= Expr == Expr
ULE        ::= Expr <=u Expr
ULT        ::= Expr <u Expr
BITMASK    ::= (Expr & C?) == C?
POPCNT     ::= popcnt(Expr) OP K?
ROT        ::= (Expr <<< K?) OP Expr
Expr       ::= Var | (Expr OP Expr) | extract(H,L,Expr) | (Expr <<< K?)
OP         ::= + | - | | | ^ | &
C?, K?     ::= /* holes for constants */
"""

import re
import z3
from typing import List, Dict, Any, Optional, Tuple, Union
from dataclasses import dataclass
from enum import Enum, auto
import logging

logger = logging.getLogger(__name__)


class AtomType(Enum):
    """Types of atomic predicates"""
    EQ = auto()         # expr == expr
    ULE = auto()        # expr <=u expr  
    ULT = auto()        # expr <u expr
    BITMASK = auto()    # (expr & C?) == C?
    POPCNT = auto()     # popcnt(expr) OP K?
    ROT = auto()        # (expr <<< K?) OP expr


class OpType(Enum):
    """Binary operations"""
    ADD = auto()        # +
    SUB = auto()        # -
    OR = auto()         # |
    XOR = auto()        # ^
    AND = auto()        # &


@dataclass
class Hole:
    """Represents a hole (unknown constant) in a template"""
    name: str
    bit_width: int
    hole_type: str = 'constant'  # 'constant', 'shift', 'mask'
    
    def to_z3_var(self) -> z3.ExprRef:
        """Convert hole to Z3 variable"""
        return z3.BitVec(self.name, self.bit_width)


@dataclass
class TemplateExpr:
    """Template expression with holes"""
    expr_type: str  # 'var', 'binop', 'extract', 'rotate', 'hole', 'const'
    value: Any = None
    left: Optional['TemplateExpr'] = None
    right: Optional['TemplateExpr'] = None
    op: Optional[OpType] = None
    high: Optional[int] = None
    low: Optional[int] = None
    shift: Optional[Union[int, Hole]] = None


@dataclass
class TemplateAtom:
    """Atomic predicate in template"""
    atom_type: AtomType
    left: Optional[TemplateExpr] = None
    right: Optional[TemplateExpr] = None
    op: Optional[OpType] = None
    constant: Optional[Union[int, Hole]] = None
    mask: Optional[Union[int, Hole]] = None


@dataclass
class TemplateInvariant:
    """Complete template invariant"""
    atoms: List[TemplateAtom]
    holes: List[Hole]
    conjunction: bool = True  # True for &&, False for ||


class TemplateParser:
    """Simplified parser for template strings"""
    
    def __init__(self, bit_width: int = 32):
        self.bit_width = bit_width
        self.variables = {}
        self.hole_counter = 0
        
    def set_variables(self, variables: Dict[str, z3.ExprRef]):
        """Set available program variables"""
        self.variables = variables
        
    def parse_template(self, template_str: str) -> Optional[TemplateInvariant]:
        """Parse template string into TemplateInvariant"""
        try:
            # Normalize template string
            template_str = self._normalize(template_str)
            
            # Determine conjunction/disjunction
            conjunction = '&&' in template_str
            separator = '&&' if conjunction else '||'
            
            # Split into atoms
            atom_strs = [s.strip() for s in template_str.split(separator)]
            
            atoms = []
            holes = []
            
            for atom_str in atom_strs:
                atom, atom_holes = self._parse_atom(atom_str)
                if atom:
                    atoms.append(atom)
                    holes.extend(atom_holes)
            
            return TemplateInvariant(atoms, holes, conjunction) if atoms else None
            
        except Exception as e:
            logger.error(f"Failed to parse template: {e}")
            return None
    
    def _normalize(self, template_str: str) -> str:
        """Normalize template string"""
        normalizations = {
            '≤u': '<=u', '<u': '<u', '∧': '&&', '∨': '||',
            '⋘': '<<<', '⋙': '>>>'
        }
        for old, new in normalizations.items():
            template_str = template_str.replace(old, new)
        return template_str
    
    def _parse_atom(self, atom_str: str) -> Tuple[Optional[TemplateAtom], List[Hole]]:
        """Parse single atomic predicate"""
        holes = []
        
        # Bitmask pattern: (expr & C?) == C?
        bitmask_match = re.match(r'\((.+?)\s*&\s*([^)]+)\)\s*==\s*(.+)', atom_str)
        if bitmask_match:
            expr = self._parse_expr(bitmask_match.group(1))
            mask = self._parse_hole_or_const(bitmask_match.group(2), holes)
            const = self._parse_hole_or_const(bitmask_match.group(3), holes)
            return TemplateAtom(AtomType.BITMASK, expr, None, None, const, mask), holes
        
        # Population count: popcnt(expr) OP K?
        popcnt_match = re.match(r'popcnt\((.+?)\)\s*([+\-&|^])\s*(.+)', atom_str)
        if popcnt_match:
            expr = self._parse_expr(popcnt_match.group(1))
            op = self._parse_op(popcnt_match.group(2))
            const = self._parse_hole_or_const(popcnt_match.group(3), holes)
            return TemplateAtom(AtomType.POPCNT, expr, None, op, const), holes
        
        # Rotation: (expr <<< K?) OP expr
        rot_match = re.match(r'\((.+?)\s*<<<\s*([^)]+)\)\s*([+\-&|^])\s*(.+)', atom_str)
        if rot_match:
            left_expr = self._parse_expr(rot_match.group(1))
            shift = self._parse_hole_or_const(rot_match.group(2), holes)
            op = self._parse_op(rot_match.group(3))
            right_expr = self._parse_expr(rot_match.group(4))
            # Create rotation expression
            rot_expr = TemplateExpr('rotate', left=left_expr, shift=shift)
            return TemplateAtom(AtomType.ROT, rot_expr, right_expr, op), holes
        
        # Comparison operators
        for op_str, atom_type in [('<=u', AtomType.ULE), ('<u', AtomType.ULT), ('==', AtomType.EQ)]:
            if op_str in atom_str:
                parts = atom_str.split(op_str, 1)
                if len(parts) == 2:
                    left = self._parse_expr(parts[0].strip())
                    right = self._parse_expr(parts[1].strip())
                    return TemplateAtom(atom_type, left, right), holes
        
        return None, holes
    
    def _parse_expr(self, expr_str: str) -> TemplateExpr:
        """Parse expression string"""
        expr_str = expr_str.strip()
        
        # Variable
        if expr_str in self.variables:
            return TemplateExpr('var', value=expr_str)
        
        # Constant
        if expr_str.isdigit() or (expr_str.startswith('0x') and len(expr_str) > 2):
            value = int(expr_str, 16) if expr_str.startswith('0x') else int(expr_str)
            return TemplateExpr('const', value=value)
        
        # Hole
        if expr_str.endswith('?'):
            hole = Hole(f"hole_{self.hole_counter}", self.bit_width)
            self.hole_counter += 1
            return TemplateExpr('hole', value=hole)
        
        # Binary operation (simplified parsing)
        for op_str, op_type in [('+', OpType.ADD), ('-', OpType.SUB), ('|', OpType.OR), 
                               ('^', OpType.XOR), ('&', OpType.AND)]:
            if op_str in expr_str:
                parts = expr_str.split(op_str, 1)
                if len(parts) == 2:
                    left = self._parse_expr(parts[0].strip())
                    right = self._parse_expr(parts[1].strip())
                    return TemplateExpr('binop', left=left, right=right, op=op_type)
        
        # Default: treat as variable
        return TemplateExpr('var', value=expr_str)
    
    def _parse_hole_or_const(self, s: str, holes: List[Hole]) -> Union[int, Hole]:
        """Parse hole or constant"""
        s = s.strip()
        if s.endswith('?'):
            hole = Hole(f"hole_{self.hole_counter}", self.bit_width)
            self.hole_counter += 1
            holes.append(hole)
            return hole
        elif s.isdigit():
            return int(s)
        elif s.startswith('0x'):
            return int(s, 16)
        else:
            # Default hole
            hole = Hole(f"hole_{self.hole_counter}", self.bit_width)
            self.hole_counter += 1
            holes.append(hole)
            return hole
    
    def _parse_op(self, op_str: str) -> OpType:
        """Parse operator string"""
        op_map = {'+': OpType.ADD, '-': OpType.SUB, '|': OpType.OR, 
                 '^': OpType.XOR, '&': OpType.AND}
        return op_map.get(op_str, OpType.ADD)
    
    def template_to_z3(self, template: TemplateInvariant) -> Tuple[z3.ExprRef, List[z3.ExprRef]]:
        """Convert template to Z3 expression"""
        atom_exprs = []
        hole_vars = []
        
        for atom in template.atoms:
            atom_expr = self._atom_to_z3(atom)
            if atom_expr is not None:
                atom_exprs.append(atom_expr)
        
        # Collect hole variables
        for hole in template.holes:
            hole_vars.append(hole.to_z3_var())
        
        if not atom_exprs:
            return z3.BoolVal(True), hole_vars
        
        # Combine atoms
        if template.conjunction:
            result = z3.And(*atom_exprs)
        else:
            result = z3.Or(*atom_exprs)
        
        return result, hole_vars
    
    def _atom_to_z3(self, atom: TemplateAtom) -> Optional[z3.ExprRef]:
        """Convert atomic predicate to Z3"""
        if atom.atom_type == AtomType.EQ:
            left = self._expr_to_z3(atom.left)
            right = self._expr_to_z3(atom.right)
            return left == right
        elif atom.atom_type == AtomType.ULE:
            left = self._expr_to_z3(atom.left)
            right = self._expr_to_z3(atom.right)
            return z3.ULE(left, right)
        elif atom.atom_type == AtomType.ULT:
            left = self._expr_to_z3(atom.left)
            right = self._expr_to_z3(atom.right)
            return z3.ULT(left, right)
        elif atom.atom_type == AtomType.BITMASK:
            expr = self._expr_to_z3(atom.left)
            mask = atom.mask.to_z3_var() if isinstance(atom.mask, Hole) else z3.BitVecVal(atom.mask, self.bit_width)
            const = atom.constant.to_z3_var() if isinstance(atom.constant, Hole) else z3.BitVecVal(atom.constant, self.bit_width)
            return (expr & mask) == const
        elif atom.atom_type == AtomType.POPCNT:
            expr = self._expr_to_z3(atom.left)
            popcnt = self._popcount_to_z3(expr)
            const = atom.constant.to_z3_var() if isinstance(atom.constant, Hole) else z3.BitVecVal(atom.constant, self.bit_width)
            
            if atom.op == OpType.ADD:
                return popcnt + const
            elif atom.op == OpType.SUB:
                return popcnt - const
            else:
                return popcnt == const
        
        return None
    
    def _expr_to_z3(self, expr: TemplateExpr) -> z3.ExprRef:
        """Convert template expression to Z3"""
        if expr.expr_type == 'var':
            return self.variables.get(expr.value, z3.BitVec(expr.value, self.bit_width))
        elif expr.expr_type == 'const':
            return z3.BitVecVal(expr.value, self.bit_width)
        elif expr.expr_type == 'hole':
            return expr.value.to_z3_var()
        elif expr.expr_type == 'binop':
            left = self._expr_to_z3(expr.left)
            right = self._expr_to_z3(expr.right)
            
            if expr.op == OpType.ADD:
                return left + right
            elif expr.op == OpType.SUB:
                return left - right
            elif expr.op == OpType.OR:
                return left | right
            elif expr.op == OpType.XOR:
                return left ^ right
            elif expr.op == OpType.AND:
                return left & right
        elif expr.expr_type == 'rotate':
            base = self._expr_to_z3(expr.left)
            shift = expr.shift.to_z3_var() if isinstance(expr.shift, Hole) else z3.BitVecVal(expr.shift, self.bit_width)
            return z3.RotateLeft(base, shift)
        
        return z3.BitVec("unknown", self.bit_width)
    
    def _popcount_to_z3(self, expr: z3.ExprRef) -> z3.ExprRef:
        """Convert population count to Z3 (simplified)"""
        # Simplified popcount for small bit widths
        if self.bit_width <= 8:
            bits = [z3.Extract(i, i, expr) for i in range(self.bit_width)]
            return z3.Sum([z3.ZeroExt(self.bit_width - 1, bit) for bit in bits])
        else:
            # For larger bit widths, use uninterpreted function
            popcount_func = z3.Function('popcount', z3.BitVecSort(self.bit_width), z3.BitVecSort(self.bit_width))
            return popcount_func(expr)


# Simplified grammar class
class TemplateGrammar:
    """Simplified template grammar validation"""
    
    def __init__(self, bit_width: int = 32):
        self.bit_width = bit_width
        
    def validate_template(self, template: TemplateInvariant) -> bool:
        """Basic template validation"""
        return len(template.atoms) > 0 and all(atom.atom_type in AtomType for atom in template.atoms) 