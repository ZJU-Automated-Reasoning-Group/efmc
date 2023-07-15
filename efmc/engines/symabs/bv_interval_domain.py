"""Main class definition for the Intervals conjunctive domain.
"""
import z3
from efmc.engines.symabs.abstract_domain import Z3VariablesDomain
from efmc.engines.symabs.bv_interval_state import Interval, IntervalAbstractState


class IntervalDomain(Z3VariablesDomain):
    """Represents an abstract space over the intervals of variables.
    """

    def __init__(self, variables):
        """Constructs a new IntervalDomain, with variables named in variables.

        variables should be a list of variable names
        """
        Z3VariablesDomain.__init__(self, variables, z3.Int)

    def join(self, elements):
        """Returns the join of a set of abstract states.

        join([ alpha_1, alpha_2, ..., alpha_n ]) is the smallest alpha
        containing all alpha_1, ..., alpha_n. It may not be in elements.
        """
        joined = self.bottom
        for state in elements:
            for name in self.variables:
                joined_interval = joined.interval_of(name)
                state_interval = state.interval_of(name)
                union = joined_interval.union(state_interval)
                joined.set_interval(name, union)
        return joined

    def meet(self, elements):
        """Returns the meet of a set of abstract states.

        join([ alpha_1, alpha_2, ..., alpha_n ]) is the greatest alpha
        contained by all alpha_1, ..., alpha_n. It may not be in elements.
        """
        met = self.top
        for state in elements:
            for name in self.variables:
                met_interval = met.interval_of(name)
                state_interval = state.interval_of(name)
                intersection = met_interval.intersection(state_interval)
                met.set_interval(name, intersection)
        return met

    @property
    def top(self):
        """Returns the least upper bound of the entire abstract space.
        """
        top_interval = Interval(float("-inf"), float("inf"))
        return IntervalAbstractState(
            dict({name: top_interval for name in self.variables}))

    @property
    def bottom(self):
        """Returns the greatest lower bound of the entire abstract space.
        """
        bottom_interval = Interval(float("inf"), float("-inf"))
        return IntervalAbstractState(
            dict({name: bottom_interval for name in self.variables}))
