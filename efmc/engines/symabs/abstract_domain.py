"""Abstract interfaces"""

import z3

class ConjunctiveDomain:
    """Represents a conjunctive domain.
    """

    def logic_and(self, formulas):
        """Returns the logical and of the given formulas.
        """
        raise NotImplementedError

    def logic_not(self, formula):
        """Returns the logical negation of the given formula.
        """
        raise NotImplementedError

    def join(self, elements):
        """Returns the least-upper-bound for elements.
        Elements should be a list of AbstractElements. The existence of such an
        upper bound is guaranteed by Definition 3.1 for a complete lattice.
        """
        raise NotImplementedError

    def meet(self, elements):
        """Returns the greatest-lower-bound for elements.
        Elements should be a list of AbstractElements. The existence of such a
        lower bound is guaranteed by Definition 3.1 for a complete lattice.
        """
        raise NotImplementedError

    @property
    def top(self):
        """Returns the least-upper-bound of the entire abstract space.
        Guaranteed by Definition 3.1
        """
        raise NotImplementedError

    @property
    def bottom(self):
        """Returns the greatest-lower-bound of the entire abstract space.
        Guaranteed by Definition 3.1
        """
        raise NotImplementedError

    def translate(self, translation):
        """Rename variables in the abstract space definition.
        Used in frontend/program.py to deal with "primes." We might encode x +=
        y as x' = x + y, y' = y, but the user will give us a domain in terms of
        x and y (which implicitly should refer to x' and y' at the end of the
        program snippet). So we translate the abstract domain given by the user
        in terms of x, y by the translation dictionary {"x": "x'", "y": "y'"}.
        Note that we use AbstractState.translate(...) to translate back to the
        user's preferred naming (x, y).
        """
        raise NotImplementedError


# pylint: disable=abstract-method
class Z3VariablesDomain(ConjunctiveDomain):
    """Represents an abstract space modelable by Z3.
    """

    def __init__(self, variables, variable_type=z3.Int,
                 build_z3_variables=True):
        """Constructs a new Z3VariablesDomain, with variables @variables.

        Arguments
        =========
        - @variables should be a list of variable names.
        - @variable_type is the z3 variable type that should be used.
        """
        self.variables = variables
        self.variable_type = variable_type
        if build_z3_variables:
            self.z3_variables = dict((name, variable_type(name))
                                     for name in self.variables)
        else:
            self.z3_variables = None

    def z3_variable(self, name):
        """Returns the Z3 variable associated with name.
        """
        return self.z3_variables[name]

    def logic_and(self, formulas):
        """Returns the logical and of the given formulas.
        """
        return z3.And(formulas)

    def logic_not(self, formula):
        """Returns the logical negation of the given formula.
        """
        return z3.Not(formula)

    def translate(self, translation):
        return type(self)(list(map(translation.__getitem__, self.variables)))


