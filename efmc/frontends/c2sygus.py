"""
C to SyGuS converter for verification.

Converts simple C programs with loops and assertions into SyGuS format
for verification using EFMC's verification engines.
"""
import re
import logging
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass

logger = logging.getLogger(__name__)


@dataclass
class Variable:
    """Represents a variable in the C program."""
    name: str
    c_type: str
    initial_value: Optional[str] = None

    @property
    def smt_type(self) -> str:
        """Get SMT-LIB type for this variable."""
        return {'bool': 'Bool', 'float': 'Real', 'double': 'Real'}.get(self.c_type, 'Int')


class CToSyGuSConverter:
    """Converts C programs to SyGuS invariant synthesis format."""
    
    def __init__(self):
        self.variables: List[Variable] = []
        self.variable_map: Dict[str, Variable] = {}
        self.assumptions: List[str] = []
        self.loop_condition: str = ""
        self.loop_body: List[str] = []
        self.assertion: str = ""
        self.errors: List[str] = []

    def reset(self):
        """Reset converter state for new conversion."""
        for attr in ['variables', 'assumptions', 'loop_body', 'errors']:
            getattr(self, attr).clear()
        self.variable_map.clear()
        self.loop_condition = self.assertion = ""

    def parse_variables(self, c_code: str) -> None:
        """Parse variable declarations from C code."""
        pattern = r'(int|bool|char|float|double)\s+([a-zA-Z_][a-zA-Z0-9_]*(?:\s*=\s*[^,;]+)?(?:\s*,\s*[a-zA-Z_][a-zA-Z0-9_]*(?:\s*=\s*[^,;]+)?)*)\s*;'
        
        for match in re.finditer(pattern, c_code):
            var_type = match.group(1)
            var_decl = match.group(2)
            
            for var_part in var_decl.split(','):
                var_part = var_part.strip()
                if '=' in var_part:
                    var_name, initial_value = var_part.split('=', 1)
                    var_name, initial_value = var_name.strip(), initial_value.strip()
                else:
                    var_name, initial_value = var_part.strip(), None
                
                if var_name and var_name not in self.variable_map:
                    variable = Variable(var_name, var_type, initial_value)
                    self.variables.append(variable)
                    self.variable_map[var_name] = variable
                    
                    if initial_value:
                        if initial_value.startswith('-'):
                            self.assumptions.append(f"(= {var_name} (- {initial_value[1:]}))")
                        else:
                            self.assumptions.append(f"(= {var_name} {initial_value})")

    def parse_assumptions(self, c_code: str) -> None:
        """Parse assume statements from C code."""
        patterns = [r'assume\s*\(\s*(.+?)\s*\)\s*;', r'__assume\s*\(\s*(.+?)\s*\)\s*;', r'ASSUME\s*\(\s*(.+?)\s*\)\s*;']
        
        for pattern in patterns:
            for match in re.finditer(pattern, c_code):
                try:
                    self.assumptions.append(self.translate_c_expr_to_smt(match.group(1).strip()))
                except Exception as e:
                    self.errors.append(f"Failed to parse assumption '{match.group(1)}': {e}")

    def parse_loop(self, c_code: str) -> None:
        """Parse while loop from C code."""
        # Try complex pattern first, then simple pattern
        patterns = [
            r'while\s*\(\s*(.+?)\s*\)\s*\{((?:[^{}]++|\{(?:[^{}]++|\{[^{}]*\})*\})*)\}',
            r'while\s*\(\s*(.+?)\s*\)\s*([^;]+;)'
        ]
        
        for pattern in patterns:
            match = re.search(pattern, c_code, re.DOTALL)
            if match:
                self.loop_condition = match.group(1).strip()
                loop_body = match.group(2).strip()
                
                if pattern == patterns[0]:  # Complex pattern
                    self.parse_loop_body(loop_body)
                else:  # Simple pattern
                    self.loop_body.append(loop_body)
                break

    def parse_loop_body(self, body: str) -> None:
        """Parse statements in loop body."""
        # Remove comments and split into statements
        body = re.sub(r'//.*$|/\*.*?\*/', '', body, flags=re.MULTILINE | re.DOTALL)
        
        statements = []
        current_stmt = ""
        brace_count = 0
        
        for char in body:
            current_stmt += char
            if char == '{':
                brace_count += 1
            elif char == '}':
                brace_count -= 1
            elif char == ';' and brace_count == 0:
                stmt = current_stmt.strip().rstrip(';').strip()
                if stmt:
                    statements.append(stmt)
                current_stmt = ""
        
        # Handle remaining statement
        if current_stmt.strip():
            stmt = current_stmt.strip().rstrip(';').strip()
            if stmt:
                statements.append(stmt)
        
        # Validate and add statements
        assignment_patterns = [
            r'^[a-zA-Z_][a-zA-Z0-9_]*\s*=\s*.+$',  # x = expr
            r'^[a-zA-Z_][a-zA-Z0-9_]*\s*\+=\s*.+$', # x += expr
            r'^[a-zA-Z_][a-zA-Z0-9_]*\s*-=\s*.+$',  # x -= expr
            r'^[a-zA-Z_][a-zA-Z0-9_]*\s*\*=\s*.+$', # x *= expr
            r'^[a-zA-Z_][a-zA-Z0-9_]*\s*/=\s*.+$',  # x /= expr
            r'^[a-zA-Z_][a-zA-Z0-9_]*\+\+$|^[a-zA-Z_][a-zA-Z0-9_]*--$',  # x++, x--
            r'^\+\+[a-zA-Z_][a-zA-Z0-9_]*$|^--[a-zA-Z_][a-zA-Z0-9_]*$'   # ++x, --x
        ]
        
        for stmt in statements:
            if stmt and not stmt.startswith(('//','/*')) and any(re.match(p, stmt.strip()) for p in assignment_patterns):
                self.loop_body.append(stmt)
            elif stmt:
                self.errors.append(f"Unsupported statement: {stmt}")

    def parse_assertion(self, c_code: str) -> None:
        """Parse assertion from C code."""
        patterns = [r'assert\s*\(\s*(.+?)\s*\)\s*;', r'__assert\s*\(\s*(.+?)\s*\)\s*;', r'ASSERT\s*\(\s*(.+?)\s*\)\s*;']
        
        for pattern in patterns:
            match = re.search(pattern, c_code)
            if match:
                try:
                    self.assertion = self.translate_c_expr_to_smt(match.group(1).strip())
                    return
                except Exception as e:
                    self.errors.append(f"Failed to parse assertion '{match.group(1)}': {e}")

    def translate_c_expr_to_smt(self, expr: str) -> str:
        """Translate C expressions to SMT-LIB format."""
        if not expr.strip():
            return "true"
        
        expr = ' '.join(expr.split())  # Normalize whitespace
        
        # Handle negative numbers first
        expr = re.sub(r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*==\s*-(\d+)', r'(= \1 (- \2))', expr)
        expr = re.sub(r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*!=\s*-(\d+)', r'(not (= \1 (- \2)))', expr)
        expr = re.sub(r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*(<=|>=|<|>)\s*-(\d+)', r'(\2 \1 (- \3))', expr)
        
        # Standard operator translations
        translations = [
            # Comparison operators
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*==\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))', r'(= \1 \2)'),
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*!=\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))', r'(not (= \1 \2))'),
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*(<=|>=|<|>)\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))', r'(\2 \1 \3)'),
            
            # Logical operators
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\([^)]+\))\s*&&\s*([a-zA-Z_][a-zA-Z0-9_]*|\([^)]+\))', r'(and \1 \2)'),
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\([^)]+\))\s*\|\|\s*([a-zA-Z_][a-zA-Z0-9_]*|\([^)]+\))', r'(or \1 \2)'),
            (r'!\s*([a-zA-Z_][a-zA-Z0-9_]*|\([^)]+\))', r'(not \1)'),
            
            # Arithmetic operators
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*\+\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*\+\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))', r'(+ \1 \2 \3)'),
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*\+\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))', r'(+ \1 \2)'),
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*-\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))', r'(- \1 \2)'),
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*\*\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))', r'(* \1 \2)'),
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*/\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))', r'(div \1 \2)'),
            (r'([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))\s*%\s*([a-zA-Z_][a-zA-Z0-9_]*|\d+|\([^)]+\))', r'(mod \1 \2)'),
        ]
        
        for pattern, replacement in translations:
            expr = re.sub(pattern, replacement, expr)
        
        return expr.replace('true', 'true').replace('false', 'false')

    def translate_assignment(self, assignment: str) -> Tuple[str, str]:
        """Translate C assignment to SMT-LIB equality."""
        assignment = assignment.strip()
        
        # Handle different assignment operators
        if '+=' in assignment:
            lhs, rhs = assignment.split('+=', 1)
            return lhs.strip(), f"(+ {lhs.strip()} {self.translate_c_expr_to_smt(rhs.strip())})"
        elif '-=' in assignment:
            lhs, rhs = assignment.split('-=', 1)
            return lhs.strip(), f"(- {lhs.strip()} {self.translate_c_expr_to_smt(rhs.strip())})"
        elif '*=' in assignment:
            lhs, rhs = assignment.split('*=', 1)
            return lhs.strip(), f"(* {lhs.strip()} {self.translate_c_expr_to_smt(rhs.strip())})"
        elif '/=' in assignment:
            lhs, rhs = assignment.split('/=', 1)
            return lhs.strip(), f"(div {lhs.strip()} {self.translate_c_expr_to_smt(rhs.strip())})"
        elif '++' in assignment:
            lhs = assignment.replace('++', '').strip()
            return lhs, f"(+ {lhs} 1)"
        elif '--' in assignment:
            lhs = assignment.replace('--', '').strip()
            return lhs, f"(- {lhs} 1)"
        elif '=' in assignment:
            lhs, rhs = assignment.split('=', 1)
            lhs, rhs = lhs.strip(), rhs.strip()
            return lhs, self.translate_c_expr_to_smt(rhs)
        else:
            raise ValueError(f"Unrecognized assignment: {assignment}")

    def generate_sygus_output(self) -> str:
        """Generate the complete SyGuS output."""
        if not self.variables:
            raise ValueError("No variables found")

        # Determine logic based on variable types
        has_real = any(var.smt_type == 'Real' for var in self.variables)
        has_int = any(var.smt_type == 'Int' for var in self.variables)
        logic = "LIRA" if has_real and has_int else "LRA" if has_real else "LIA"
        
        # Build function arguments
        args = ' '.join(f"({var.name} {var.smt_type})" for var in self.variables)
        trans_args = args + ' ' + ' '.join(f"({var.name}! {var.smt_type})" for var in self.variables)

        # Generate conditions
        pre_cond = "true" if not self.assumptions else ("(and " + " ".join(self.assumptions) + ")" if len(self.assumptions) > 1 else self.assumptions[0])
        
        # Generate transition relation
        transitions = []
        updated_vars = set()
        
        for stmt in self.loop_body:
            try:
                lhs, rhs_smt = self.translate_assignment(stmt)
                if lhs in self.variable_map:
                    transitions.append(f"(= {lhs}! {rhs_smt})")
                    updated_vars.add(lhs)
            except Exception as e:
                self.errors.append(f"Failed to translate '{stmt}': {e}")

        # Add unchanged variables
        for var in self.variables:
            if var.name not in updated_vars:
                transitions.append(f"(= {var.name}! {var.name})")

        trans_cond = ' '.join(transitions)
        if self.loop_condition:
            loop_cond_smt = self.translate_c_expr_to_smt(self.loop_condition)
            trans_cond = f"(and {loop_cond_smt} {trans_cond})"

        # Generate post condition
        if self.assertion and self.loop_condition:
            loop_cond_smt = self.translate_c_expr_to_smt(self.loop_condition)
            post_cond = f"(=> (not {loop_cond_smt}) {self.assertion})"
        else:
            post_cond = self.assertion or "true"

        return f"""(set-logic {logic})

(synth-inv inv_fun ({args}))

(define-fun pre_fun ({args}) Bool
    {pre_cond})

(define-fun trans_fun ({trans_args}) Bool
    {trans_cond})

(define-fun post_fun ({args}) Bool
    {post_cond})

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
"""

    def convert(self, c_program: str) -> str:
        """Convert C program to SyGuS format."""
        self.reset()
        
        # Parse all components
        self.parse_variables(c_program)
        self.parse_assumptions(c_program)
        self.parse_loop(c_program)
        self.parse_assertion(c_program)
        
        if self.errors:
            raise ValueError("Conversion failed:\n" + "\n".join(self.errors))
        
        if not self.variables:
            raise ValueError("No variables found")
        
        return self.generate_sygus_output()


def main():
    """Example usage."""
    c_program = """
    int x, y;
    
    assume(x == -50);
    assume(y == 1);
    
    while(x < 3) {
        x = x + y;
        y = y + 2;
    }
    
    assert(y > 0);
    """

    converter = CToSyGuSConverter()
    try:
        result = converter.convert(c_program)
        print("Conversion successful!")
        print(result)
    except Exception as e:
        print(f"Conversion failed: {e}")


if __name__ == "__main__":
    main()
