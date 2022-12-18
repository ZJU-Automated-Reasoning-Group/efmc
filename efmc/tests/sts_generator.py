"""
Randomly generating a transition system
"""

from efmc.tests.formula_generator import FormulaGenerator


class TransitionSystemGenerator:
    """
    TODO: how to ensure the oracle
    """
    def __int__(self):
        self.fml_gene = FormulaGenerator()
        pass

    def gen_bool_program(self):
        """Boolean program"""
        raise NotImplementedError

    def gen_lra_program(self):
        raise NotImplementedError

    def gen_lia_program(self):
        raise NotImplementedError

    def gen_auflia_program(self):
        raise NotImplementedError

    def gen_nra_program(self):
        raise NotImplementedError

    def gen_nia_program(self):
        raise NotImplementedError

    def gen_bv_program(self):
        raise NotImplementedError