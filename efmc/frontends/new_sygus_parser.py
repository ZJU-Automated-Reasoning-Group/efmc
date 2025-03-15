"""
SyGuS Invariant Track Parser based on a simple S-expression parser.

This parser is designed to handle inputs specifically in the style of the SyGuS invariant track.
It can potentially be adapted for SyGuS (PBE) with minor modifications. To maintain independence,
this file does not import other files from the project.

Dependencies:
    - z3-solver

Usage:
    Instantiate the `SyGusInVParser` with the input string and specify whether to cast integers to reals.
    Use the `get_transition_system` method to retrieve the parsed transition system components.
"""

import z3
from typing import Union, List, Tuple, Optional, Dict, Set

# Define type aliases for clarity
Symbol = str
Number = Union[int, float]
Atom = Union[Symbol, Number]
SExpression = Union[Atom, List['SExpression']]


def input_to_list(string: str) -> List[str]:
    """
    Parse a .sl file content into a list of S-Expressions.

    Args:
        string (str): The content of the .sl file.

    Returns:
        List[str]: A list where each element is a single S-expression string.
    """
    n = 0
    result = []
    s = ""
    for c in string:
        if c == "(":
            n += 1
        elif c == ")":
            n -= 1
        if c not in "\n":
            s += c
        if n == 0 and s.strip():
            result.append(s.strip())
            s = ""
    return result


def tokenize(chars: str) -> List[str]:
    """
    Convert a string of characters into a list of tokens.

    Args:
        chars (str): The input string.

    Returns:
        List[str]: A list of tokens.
    """
    # Handle quotes properly and ensure spaces around parentheses
    chars = chars.replace('(', ' ( ').replace(')', ' ) ')
    tokens = []
    current_token = ""
    in_quote = False

    for c in chars:
        if c == '"':
            in_quote = not in_quote
            current_token += c
        elif c.isspace() and not in_quote:
            if current_token:
                tokens.append(current_token)
                current_token = ""
        else:
            current_token += c

    if current_token:
        tokens.append(current_token)

    return tokens


def parse_sexpression(program: str) -> SExpression:
    """
    Parse a string into an S-expression.

    Args:
        program (str): The S-expression string.

    Returns:
        SExpression: The parsed S-expression.
    """
    return read_from_tokens(tokenize(program))


def read_from_tokens(tokens: List[str]) -> Optional[SExpression]:
    """
    Read an expression from a sequence of tokens.

    Args:
        tokens (List[str]): The list of tokens.

    Returns:
        Optional[SExpression]: The parsed S-expression or None if tokens are empty.
    """
    if not tokens:
        raise SyntaxError('Unexpected EOF while reading')

    token = tokens.pop(0)
    if token == '(':
        L = []
        while tokens and tokens[0] != ')':
            L.append(read_from_tokens(tokens))
        if not tokens:
            raise SyntaxError('Missing ")"')
        tokens.pop(0)  # Remove ')'
        return L
    elif token == ')':
        raise SyntaxError('Unexpected ")"')
    else:
        return atom(token)


def atom(token: str) -> Atom:
    """
    Convert a token to its atomic form: number or symbol.

    Args:
        token (str): The token string.

    Returns:
        Atom: An integer, float, or symbol.
    """
    # Handle quoted strings
    if token.startswith('"') and token.endswith('"'):
        return token[1:-1]
    try:
        return int(token)
    except ValueError:
        try:
            return float(token)
        except ValueError:
            return Symbol(token)


def get_start(cmd: SExpression) -> str:
    """
    Extract the start symbol from the synth-fun command.

    Args:
        cmd (SExpression): The S-expression representing the synth-fun command.

    Returns:
        str: The start symbol.
    """
    assert cmd[0] == "synth-fun", "Expected 'synth-fun' command"
    return cmd[4][0]


def get_nonterminals(cmd: SExpression) -> Tuple[Set[str], Dict[str, str]]:
    """
    Extract nonterminals and their types from the synth-fun command.

    Args:
        cmd (SExpression): The S-expression representing the synth-fun command.

    Returns:
        Tuple[Set[str], Dict[str, str]]: A set of nonterminals and a dictionary mapping them to their types.
    """
    nonterms = set()
    type_dict: Dict[str, str] = {}
    assert cmd[0] == "synth-fun", "Expected 'synth-fun' command"

    for elem in cmd[4]:
        nt = elem[0]
        typ = elem[1]
        nonterms.add(nt)
        type_dict[nt] = typ

    return nonterms, type_dict


def get_terms_prods(cmd: SExpression) -> Tuple[
    Set[Union[str, Tuple]], Dict[str, List[Tuple[Union[str, Tuple], List[str]]]]]:
    """
    Extract terminals and production rules from the synth-fun command.

    Args:
        cmd (SExpression): The S-expression representing the synth-fun command.

    Returns:
        Tuple containing:
            - Set of terminals (operators or constants).
            - Dictionary mapping nonterminals to their production rules.
    """
    terminals = set()
    productions: Dict[str, List[Tuple[Union[str, Tuple], List[str]]]] = {}

    for nonterm_list in cmd[5]:
        non_term = nonterm_list[0]
        product = []
        for t in nonterm_list[2]:
            nts: List[str] = []
            if isinstance(t, list):
                term = t[0]
                nts.extend(t[1:])
            else:
                term = t

            if isinstance(term, list):
                term = tuple(term)

            terminals.add(term)
            product.append((term, nts))
        productions[non_term] = product

    return terminals, productions


def get_grammar(lines: List[str]) -> Tuple[
    Set[str], Set[Union[str, Tuple]], Dict[str, List[Tuple[Union[str, Tuple], List[str]]]], str]:
    """
    Parse multiple lines of S-expressions to extract grammar components.

    Args:
        lines (List[str]): List of S-expression strings.

    Returns:
        Tuple containing nonterminals, terminals, productions, and start symbol.
    """
    s_exprs = [parse_sexpression(line) for line in lines]
    for s in s_exprs:
        if isinstance(s, list) and s:
            if s[0] == "synth-fun":
                start_sym = get_start(s)
                nonterminals, type_dict = get_nonterminals(s)
                terminals, productions = get_terms_prods(s)
                return nonterminals, terminals, productions, start_sym
    raise ValueError("No 'synth-fun' command found in the input.")


# Predefined function names for different roles
PRE_FUNC_NAMES = {"pre_fun", "PreF", "pre-f"}
TRANS_FUNC_NAMES = {"trans_fun", "TransF", "trans-f"}
POST_FUNC_NAMES = {"post_fun", "PostF", "post-f"}


class SyGusInVParser:
    """
    Parser for SyGuS Invariant Track problems.
    """

    def __init__(self, inputs: str, to_real: bool = False):
        """
        Initialize the parser with input data.

        Args:
            inputs (str): The SyGuS input string.
            to_real (bool): Whether to cast integer types to reals.
        """
        self.to_real = to_real
        self.logic: Optional[str] = None
        self.inv_vars: List[Tuple[str, str]] = []
        self.all_vars: List[Tuple[str, Union[str, List]]] = []
        self.inv_arity: int = 0
        self.pre_fun_body: str = ""
        self.trans_fun_body: str = ""
        self.post_fun_body: str = ""

        self.nonterminals: Set[str] = set()
        self.terminals: Set[Union[str, Tuple]] = set()
        self.productions: Dict[str, List[Tuple[Union[str, Tuple], List[str]]]] = {}
        self.start_symbol: str = ""

        self.init_symbols(inputs)

    def to_sexpr_misc(self, expr: SExpression) -> List[str]:
        """
        Convert an S-expression into a string suitable for SMT.

        Args:
            expr (SExpression): The S-expression.

        Returns:
            List[str]: The expression represented as a list of strings.
        """
        res = []
        if isinstance(expr, list):
            res.append("(")
            for element in expr:
                res.extend(self.to_sexpr_misc(element))
            res.append(")")
        else:
            if isinstance(expr, int) and self.to_real:
                expr_str = f"{expr}.0"
            else:
                expr_str = str(expr)
            res.append(expr_str)
        return res

    def to_sexpr(self, expr: SExpression) -> str:
        """
        Convert an S-expression into its string representation.

        Args:
            expr (SExpression): The S-expression.

        Returns:
            str: The string representation.
        """
        return " ".join(self.to_sexpr_misc(expr))

    def init_symbols(self, inputs: str):
        """
        Initialize symbols by parsing the input S-expressions.

        Args:
            inputs (str): The SyGuS input string.
        """
        lines = input_to_list(inputs)
        for line in lines:
            s_expr = parse_sexpression(line)
            if isinstance(s_expr, list):
                cmd_name = s_expr[0]
                if cmd_name == "set-logic":
                    self.logic = s_expr[1]
                elif cmd_name == "synth-inv":
                    self.inv_arity = len(s_expr[2])
                elif cmd_name == "define-fun":
                    self.process_func(s_expr)
                elif cmd_name == "inv-constraint":
                    break  # Stop processing after constraints
        # Optionally, handle post-processing or validations here

    def process_func(self, s_expr: SExpression):
        """
        Process a 'define-fun' command to extract function bodies and variables.

        Args:
            s_expr (SExpression): The 'define-fun' S-expression.
        """
        assert isinstance(s_expr, list) and len(s_expr) >= 5, "Invalid 'define-fun' structure"
        func_name = s_expr[1]
        if func_name in PRE_FUNC_NAMES:
            self.pre_fun_body = self.to_sexpr(s_expr[4])
            self.inv_vars = s_expr[2]
        elif func_name in TRANS_FUNC_NAMES:
            self.trans_fun_body = self.to_sexpr(s_expr[4])
            self.all_vars = s_expr[2]
        elif func_name in POST_FUNC_NAMES:
            self.post_fun_body = self.to_sexpr(s_expr[4])
        else:
            raise ValueError(f"Unrecognized function name: {func_name}")

    def get_transition_system(self) -> Tuple[List[z3.ExprRef], z3.ExprRef, z3.ExprRef, z3.ExprRef]:
        """
        Construct the transition system components for Z3.

        Returns:
            Tuple containing:
                - List of Z3 variables.
                - Initial constraints.
                - Transition constraints.
                - Post constraints.
        """
        init_constraints: List[str] = []
        trans_constraints: List[str] = []
        post_constraints: List[str] = []

        for var in self.all_vars:
            var_name, var_type = var[0], var[1]
            if isinstance(var_type, list):
                # Handle complex types like arrays or bit-vectors
                type_str = " ".join(map(str, var_type))
                final_type = f"({type_str})"
            else:
                if self.to_real and var_type != "Real":
                    final_type = "Real"
                else:
                    final_type = var_type

            init_constraints.append(f"(declare-const {var_name} {final_type})")
            trans_constraints.append(f"(declare-const {var_name} {final_type})")
            post_constraints.append(f"(declare-const {var_name} {final_type})")

        # Add assertions for pre, trans, and post functions
        init_constraints.append(f"(assert {self.pre_fun_body})")
        trans_constraints.append(f"(assert {self.trans_fun_body})")
        post_constraints.append(f"(assert {self.post_fun_body})")

        # Parse SMT2 strings using Z3
        init = z3.parse_smt2_string("\n".join(init_constraints))
        trans = z3.parse_smt2_string("\n".join(trans_constraints))
        post = z3.parse_smt2_string("\n".join(post_constraints))

        # Collect Z3 variables
        z3_vars = []
        for var_sig in self.all_vars:
            var_name, var_type = var_sig
            if isinstance(var_type, list):
                if var_type[0] == 'Array':
                    z3_var = z3.Array(var_name, z3.IntSort(), z3.IntSort())
                elif var_type[0] == '_':
                    # Handle BitVectors, e.g., ['_', 'BitVec', 32]
                    if len(var_type) >= 3 and var_type[1] == 'BitVec':
                        size = int(var_type[2])
                        z3_var = z3.BitVec(var_name, size)
                    else:
                        raise ValueError(f"Unsupported type specification: {var_type}")
                else:
                    raise ValueError(f"Unsupported complex type: {var_type}")
            else:
                if var_type == "Int":
                    z3_var = z3.Int(var_name)
                elif var_type == "Real":
                    z3_var = z3.Real(var_name)
                else:
                    raise ValueError(f"Unsupported type: {var_type}")
            z3_vars.append(z3_var)

        return z3_vars, init[0], trans[0], post[0]


def demo_parser():
    """
    Demonstration of the SyGusInVParser with sample inputs.
    """
    example_input = """(set-logic ALIA)
(synth-inv inv_fun ((x (Array Int Int)) (y Int) (n Int)))
(define-fun pre_fun ((x (Array Int Int)) (y Int) (n Int)) Bool
    (and (>= n 0) (and (= n (select x 0)) (= y 0))))
(define-fun trans_fun ((x (Array Int Int)) (y Int) (n Int) (x! (Array Int Int)) (y! Int) (n! Int)) Bool
    (and (> (select x 0) 0) (and (= n! n) (and (= y! (+ y 1)) (= x! (store x 0 (- (select x 0) 1)))))))
(define-fun post_fun ((x (Array Int Int)) (y Int) (n Int)) Bool
    (or (> (select x 0) 0) (= n (+ (select x 0) y))))
(inv-constraint inv_fun pre_fun trans_fun post_fun)
(check-synth)"""

    # Initialize the parser
    parser = SyGusInVParser(example_input, to_real=False)

    # Retrieve the transition system components
    all_vars, init, trans, post = parser.get_transition_system()

    # Display the results
    print("Declared Variables:")
    for var in all_vars:
        print(f"  {var}")

    print("\nInitial Constraints:")
    print(init)

    print("\nTransition Constraints:")
    print(trans)

    print("\nPost Constraints:")
    print(post)


if __name__ == '__main__':
    demo_parser()
