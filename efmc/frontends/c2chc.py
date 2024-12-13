"""
FIXME: not implemented yet!
"""

from typing import Dict, Set

import z3
from pycparser import c_parser, c_ast

from efmc.sts import TransitionSystem


class CToTransitionSystem:
    def __init__(self):
        self.parser = c_parser.CParser()
        self.variables: Set[str] = set()
        self.prime_variables: Set[str] = set()
        self.init_conditions = []
        self.trans_conditions = []
        self.post_conditions = []
        self.var_types: Dict[str, str] = {}

    def parse_program(self, c_code: str, post_condition: str = None) -> TransitionSystem:
        raise NotImplementedError

    def _process_ast(self, node: c_ast.Node):
        raise NotImplementedError

    def _handle_loop(self, node: c_ast.While):
        raise NotImplementedError

    def _process_declarations(self, decls):
        raise NotImplementedError


def simple_counter_loop():
    c_code = """
        int x = 0;
        while (x < 10) {
            x = x + 1;
        }
        """
    post_condition = "x == 10"

    parser = CToTransitionSystem()

    ts = parser.parse_program(c_code, post_condition)



simple_counter_loop()
