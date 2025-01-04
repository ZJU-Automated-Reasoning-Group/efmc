"""
New TransitionSystem
"""
from typing import List, Dict, Any, Tuple, Optional
from collections import defaultdict
from itertools import product


class TransitionSystem:
    def __init__(self):
        self.states = set()
        self.initial_states = set()
        self.transitions = defaultdict(list)
        self.labels = defaultdict(set)

    def add_state(self, state: Any, initial: bool = False):
        self.states.add(state)
        if initial:
            self.initial_states.add(state)

    def add_transition(self, source: Any, target: Any, action: Any):
        self.transitions[source].append((action, target))

    def add_label(self, state: Any, label: Any):
        self.labels[state].add(label)

    def get_successors(self, state: Any, action: Optional[Any] = None) -> List[Any]:
        if action is None:
            return [target for _, target in self.transitions[state]]
        return [target for act, target in self.transitions[state] if act == action]

    def get_labels(self, state: Any) -> set:
        return self.labels[state]

    def is_initial(self, state: Any) -> bool:
        return state in self.initial_states
    