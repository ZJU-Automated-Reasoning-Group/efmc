"""
FIXME: by LLM, to check
C to SyGuS converter for verification.

This module converts simple C programs with loops and assertions into SyGuS format
for verification using EFMC's verification engines.
"""
import re
import logging
from typing import List, Dict, Tuple, Optional

logger = logging.getLogger(__name__)


class CToSyGuSConverter:
    def __init__(self):
        self.variables = []
        self.variable_types = {}
        self.assumptions = []
        self.loop_condition = ""
        self.loop_body = []
        self.assertion = ""
        self.sygus_template = """
(set-logic {logic})

;; Variable declarations
{declarations}

;; Invariant function declaration
(synth-inv inv ({inv_args}))

;; Pre-condition (from assumptions)
(define-fun pre ({args}) Bool
    {pre_cond}
)

;; Transition relation (loop body)
(define-fun trans ({args} {args_prime}) Bool
    (and
        {loop_cond}
        {trans_rel}
    )
)

;; Post-condition (from assertions)
(define-fun post ({args}) Bool
    {post_cond}
)

;; Invariant constraints
(inv-constraint inv pre trans post)

(check-synth)
"""

    def parse_variables(self, c_code: str) -> None:
        """Parse variable declarations from C code."""
        # Match variable declarations like "int x;" or "int x = 5;"
        var_pattern = r'(int|bool|char)\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*(?:=\s*([^;]+))?;'
        for match in re.finditer(var_pattern, c_code):
            var_type, var_name, initial_value = match.groups()
            self.variables.append(var_name)
            self.variable_types[var_name] = var_type
            if initial_value:
                self.assumptions.append(f"{var_name} == {initial_value}")

    def parse_assumptions(self, c_code: str) -> None:
        """Parse assume statements from C code."""
        assume_pattern = r'assume\s*\(\s*(.+?)\s*\)\s*;'
        for match in re.finditer(assume_pattern, c_code):
            self.assumptions.append(match.group(1))

    def parse_loop(self, c_code: str) -> None:
        """Parse while loop from C code."""
        # Match while loop pattern
        loop_pattern = r'while\s*\(\s*(.+?)\s*\)\s*{([\s\S]*?)}'
        match = re.search(loop_pattern, c_code)
        if match:
            self.loop_condition = match.group(1)
            loop_body = match.group(2)

            # Parse statements in loop body
            stmt_pattern = r'([^;]+);'
            for stmt_match in re.finditer(stmt_pattern, loop_body):
                stmt = stmt_match.group(1).strip()
                if stmt and not stmt.startswith('//'):
                    self.loop_body.append(stmt)

    def parse_assertion(self, c_code: str) -> None:
        """Parse assertion from C code."""
        assert_pattern = r'assert\s*\(\s*(.+?)\s*\)\s*;'
        match = re.search(assert_pattern, c_code)
        if match:
            self.assertion = match.group(1)

    def translate_c_expr_to_smt(self, expr: str) -> str:
        """Translate C expressions to SMT-LIB format."""
        # Replace C operators with SMT-LIB operators
        expr = re.sub(r'==', '=', expr)
        expr = re.sub(r'&&', 'and', expr)
        expr = re.sub(r'\|\|', 'or', expr)
        expr = re.sub(r'!([^=])', r'(not \1)', expr)
        expr = re.sub(r'!=', '(not =)', expr)

        # Handle array accesses
        expr = re.sub(r'([a-zA-Z_][a-zA-Z0-9_]*)\[([^\]]+)\]', r'(select \1 \2)', expr)

        # Handle function calls
        expr = re.sub(r'([a-zA-Z_][a-zA-Z0-9_]*)\(([^)]*)\)', r'(\1 \2)', expr)

        return expr

    def translate_assignment(self, assignment: str) -> Tuple[str, str]:
        """Translate C assignment to SMT-LIB equality."""
        parts = assignment.split('=', 1)
        if len(parts) != 2:
            raise ValueError(f"Invalid assignment: {assignment}")

        lhs = parts[0].strip()
        rhs = parts[1].strip()

        # Handle special cases like x++ or x+=1
        if '+=' in assignment:
            lhs, rhs = assignment.split('+=', 1)
            lhs = lhs.strip()
            rhs = f"{lhs} + ({rhs.strip()})"
        elif '-=' in assignment:
            lhs, rhs = assignment.split('-=', 1)
            lhs = lhs.strip()
            rhs = f"{lhs} - ({rhs.strip()})"
        elif '++' in lhs:
            lhs = lhs.replace('++', '').strip()
            rhs = f"{lhs} + 1"
        elif '--' in lhs:
            lhs = lhs.replace('--', '').strip()
            rhs = f"{lhs} - 1"

        # Translate the right-hand side to SMT-LIB
        rhs_smt = self.translate_c_expr_to_smt(rhs)

        return lhs, rhs_smt

    def generate_declarations(self) -> str:
        """Generate SMT-LIB variable declarations."""
        declarations = []
        for var in self.variables:
            c_type = self.variable_types.get(var, 'int')
            smt_type = 'Int'
            if c_type == 'bool':
                smt_type = 'Bool'
            declarations.append(f"(declare-var {var} {smt_type})")
            declarations.append(f"(declare-var {var}! {smt_type})")
        return '\n'.join(declarations)

    def generate_pre_condition(self) -> str:
        """Generate pre-condition from assumptions."""
        if not self.assumptions:
            return "true"

        smt_assumptions = [self.translate_c_expr_to_smt(assume) for assume in self.assumptions]
        if len(smt_assumptions) == 1:
            return smt_assumptions[0]
        return f"(and {' '.join(smt_assumptions)})"

    def generate_transition_relation(self) -> str:
        """Generate transition relation from loop body."""
        transitions = []

        # For each variable, add a constraint for its next value
        for var in self.variables:
            var_updated = False

            # Check if this variable is updated in the loop
            for stmt in self.loop_body:
                if re.match(rf'{var}\s*=', stmt) or re.match(rf'{var}\s*\+=', stmt) or \
                        re.match(rf'{var}\s*-=', stmt) or re.match(rf'{var}\+\+', stmt) or \
                        re.match(rf'{var}--', stmt):
                    lhs, rhs_smt = self.translate_assignment(stmt)
                    if lhs.strip() == var:
                        transitions.append(f"(= {var}! {rhs_smt})")
                        var_updated = True
                        break

            # If variable is not updated, it stays the same
            if not var_updated:
                transitions.append(f"(= {var}! {var})")

        return '\n        '.join(transitions)

    def generate_loop_condition(self) -> str:
        """Generate loop condition in SMT-LIB format."""
        return self.translate_c_expr_to_smt(self.loop_condition)

    def generate_post_condition(self) -> str:
        """Generate post-condition from assertion."""
        if not self.assertion:
            return "true"

        # The post-condition is the negation of the loop condition AND the assertion
        loop_cond_smt = self.translate_c_expr_to_smt(self.loop_condition)
        assertion_smt = self.translate_c_expr_to_smt(self.assertion)

        return f"(=> (not {loop_cond_smt}) {assertion_smt})"

    def generate_args_string(self) -> str:
        """Generate argument string for function definitions."""
        return ' '.join([f"({var} {self.get_smt_type(var)})" for var in self.variables])

    def get_smt_type(self, var: str) -> str:
        """Get SMT-LIB type for a variable."""
        c_type = self.variable_types.get(var, 'int')
        if c_type == 'bool':
            return 'Bool'
        return 'Int'

    def determine_logic(self) -> str:
        """Determine the appropriate logic based on variables and operations."""
        # For now, we'll use LIA (Linear Integer Arithmetic) as default
        return "LIA"

    def convert(self, c_program: str) -> str:
        """Convert C program to SyGuS format."""
        # Reset state
        self.variables = []
        self.variable_types = {}
        self.assumptions = []
        self.loop_condition = ""
        self.loop_body = []
        self.assertion = ""

        # Parse C program
        self.parse_variables(c_program)
        self.parse_assumptions(c_program)
        self.parse_loop(c_program)
        self.parse_assertion(c_program)

        # Generate SyGuS components
        logic = self.determine_logic()
        declarations = self.generate_declarations()
        inv_args = ' '.join([f"({var} {self.get_smt_type(var)})" for var in self.variables])
        args = self.generate_args_string()
        args_prime = ' '.join([f"({var}! {self.get_smt_type(var)})" for var in self.variables])
        pre_cond = self.generate_pre_condition()
        loop_cond = self.generate_loop_condition()
        trans_rel = self.generate_transition_relation()
        post_cond = self.generate_post_condition()

        # Fill in the template
        sygus_output = self.sygus_template.format(
            logic=logic,
            declarations=declarations,
            inv_args=inv_args,
            args=args,
            args_prime=args_prime,
            pre_cond=pre_cond,
            loop_cond=loop_cond,
            trans_rel=trans_rel,
            post_cond=post_cond
        )

        return sygus_output


# Example usage
def main():
    c_program = """
    int x;
    int y;

    assume(x == -50);
    assume(y == 1);

    while(x < 3){
        x = x + y;
        y = y + 2;
    }

    assert(y > 0);
    """

    converter = CToSyGuSConverter()
    sygus_output = converter.convert(c_program)
    print(sygus_output)


if __name__ == "__main__":
    main()
