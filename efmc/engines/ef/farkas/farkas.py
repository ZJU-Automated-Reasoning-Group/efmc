from z3 import *
from typing import List, Tuple, Dict, Any


class TransitionSystem:
    """
    Represents a transition system with variables, transitions, and program points.
    """

    def __init__(self, variables: List[str]):
        """
        Initializes the Transition System with specified variables.

        :param variables: List of variable names as strings.
        """
        self.variables = variables
        self.transitions: List[Tuple[str, str, Dict[str, Any]]] = []
        self.program_points = set()

    def add_transition(self, source: str, target: str, transformation: Dict[str, Any]):
        """
        Adds a transition to the system.

        :param source: Source program point (basic block name).
        :param target: Target program point (basic block name).
        :param transformation: Dictionary mapping variable names to their updated expressions.
        """
        self.transitions.append((source, target, transformation))
        self.program_points.add(source)
        self.program_points.add(target)

    def get_program_points(self) -> List[str]:
        """
        Returns all program points in the system.
        """
        return list(self.program_points)

    def get_variables(self) -> List[str]:
        """
        Returns all variables in the system.
        """
        return self.variables


class InvariantSynthesizer:
    """
    Synthesizes linear invariants for a given TransitionSystem using Z3.
    Supports specifying post-conditions that invariants must satisfy at designated program points.
    """

    def __init__(self, transition_system: TransitionSystem, post_condition: ExprRef = None, post_point: str = 'end'):
        """
        Initializes the Invariant Synthesizer with a Transition System and an optional post-condition.

        :param transition_system: An instance of TransitionSystem.
        :param post_condition: A Z3 Boolean expression representing the post-condition.
        :param post_point: The program point where the post-condition should hold (default is 'end').
        """
        self.transition_system = transition_system
        self.post_condition = post_condition
        self.post_point = post_point
        self.solver = Solver()
        self.invariant_vars: Dict[str, Dict[str, Real]] = {}
        self.define_invariants()
        self.add_transition_constraints()
        self.add_non_triviality_constraints()
        self.add_post_condition_constraints()

    def define_invariants(self):
        """
        Defines invariant variables for each program point.
        Assumes linear invariants of the form a*x + b*y + ... + c = 0 for each program point.
        """
        for point in self.transition_system.get_program_points():
            self.invariant_vars[point] = {}
            for var in self.transition_system.get_variables():
                # Coefficients for each variable
                self.invariant_vars[point][var] = Real(f'{point}_{var}_coeff')
            # Constant term
            self.invariant_vars[point]['c'] = Real(f'{point}_c')
            # Define the invariant equation: sum(a_i * v_i) + c = 0
            invariant_eq = Sum([self.invariant_vars[point][var] * Int(var)
                                for var in self.transition_system.get_variables()]) + self.invariant_vars[point][
                               'c'] == 0
            self.solver.add(invariant_eq)

    def add_transition_constraints(self):
        """
        Adds constraints to ensure invariants are preserved across transitions.
        For each transition, if the invariant holds before the transition,
        it should hold after applying the transformation.
        """
        for transition in self.transition_system.transitions:
            source, target, transformation = transition
            # Invariant at source: a*x + b*y + ... + c = 0
            invariant_src = Sum([self.invariant_vars[source][var] * Int(var)
                                 for var in self.transition_system.get_variables()]) + self.invariant_vars[source][
                                'c'] == 0

            # Apply transformation: define new expressions for variables
            # Create a substitution dictionary
            substitution = {}
            for var in self.transition_system.get_variables():
                if var in transformation:
                    # It is assumed that transformation[var] is a valid Z3 expression
                    substitution[var] = transformation[var]
                else:
                    # If no transformation is specified, variable remains the same
                    substitution[var] = Int(var)

            # Invariant at target after transformation
            invariant_tgt = Sum([self.invariant_vars[target][var] * substitution[var]
                                 for var in self.transition_system.get_variables()]) + self.invariant_vars[target][
                                'c'] == 0

            # Add implication: invariant_src -> invariant_tgt
            implication = Implies(invariant_src, invariant_tgt)
            self.solver.add(implication)

    def add_non_triviality_constraints(self):
        """
        Adds constraints to ensure invariants are non-trivial.
        For linear invariants, ensures that not all coefficients are zero.
        """
        for point in self.transition_system.get_program_points():
            coeffs = [self.invariant_vars[point][var] for var in self.transition_system.get_variables()]
            coeffs.append(self.invariant_vars[point]['c'])
            # At least one coefficient should be non-zero
            non_trivial = Or([coeff != 0 for coeff in coeffs])
            self.solver.add(non_trivial)

    def add_post_condition_constraints(self):
        """
        Adds constraints to ensure that the post-condition holds at the designated program point.
        Specifically, it enforces that the invariant at the post_point implies the post_condition.
        """
        if self.post_condition is not None:
            if self.post_point not in self.transition_system.program_points:
                raise ValueError(
                    f"Post-point '{self.post_point}' is not a valid program point in the transition system.")

            # Construct the invariant at post_point: a*x + b*y + ... + c = 0
            invariant_post_eq = Sum([self.invariant_vars[self.post_point][var] * Int(var)
                                     for var in self.transition_system.get_variables()]) + \
                                self.invariant_vars[self.post_point]['c'] == 0

            # Add the implication: invariant_post_eq => post_condition
            self.solver.add(Implies(invariant_post_eq, self.post_condition))

    def synthesize(self) -> Dict[str, str]:
        """
        Attempts to synthesize invariants. Returns a dictionary mapping
        program points to their invariants if successful.

        :return: Dictionary with program points as keys and invariant expressions as values.
        """
        if self.solver.check() == sat:
            model = self.solver.model()
            invariants = {}
            for point in self.transition_system.get_program_points():
                invariant_terms = []
                for var in self.transition_system.get_variables():
                    coeff = model.evaluate(self.invariant_vars[point][var], model_completion=True)
                    # Directly retrieve the fraction without checking
                    try:
                        numerator, denominator = coeff.as_fraction()
                        if denominator == 1:
                            coeff_val = numerator
                        else:
                            coeff_val = f"{numerator}/{denominator}"
                    except:
                        # Fallback to string representation if as_fraction() fails
                        coeff_val = f"{coeff}"
                    invariant_terms.append(f"{coeff_val}*{var}")
                # Constant term
                c = model.evaluate(self.invariant_vars[point]['c'], model_completion=True)
                try:
                    c_numerator, c_denominator = c.as_fraction()
                    if c_denominator == 1:
                        c_val = c_numerator
                    else:
                        c_val = f"{c_numerator}/{c_denominator}"
                except:
                    # Fallback to string representation if as_fraction() fails
                    c_val = f"{c}"
                invariant = " + ".join(invariant_terms) + f" + {c_val} = 0"
                invariants[point] = invariant
            return invariants
        else:
            raise ValueError("No invariant found.")


def main():
    # Initialize Z3 variables
    x, y = Ints('x y')

    # Define variables in the program
    variables = ['x', 'y']

    # Initialize the Transition System
    ts = TransitionSystem(variables)

    # Define program transitions
    # Example:
    # start -> loop: x' = x + 1, y' = y
    # loop -> end: x' = x, y' = y + x
    # loop -> loop: x' = x + y, y' = y

    ts.add_transition('start', 'loop', {'x': x + 1, 'y': y})
    ts.add_transition('loop', 'end', {'x': x, 'y': y + x})
    ts.add_transition('loop', 'loop', {'x': x + y, 'y': y})

    # Define the post-condition
    # For example: y > x
    post_condition = y > x

    # Initialize the Invariant Synthesizer with the post-condition
    synthesizer = InvariantSynthesizer(transition_system=ts, post_condition=post_condition, post_point='end')

    try:
        # Synthesize invariants
        invariants = synthesizer.synthesize()

        # Print the invariants
        print("Synthesized Invariants:")
        for point, invariant in invariants.items():
            print(f"  {point}: {invariant}")
    except ValueError as e:
        print(str(e))


if __name__ == "__main__":
    main()

