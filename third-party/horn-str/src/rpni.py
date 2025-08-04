import automata
from graphviz import Digraph


class RPNI:
    def __init__(self, positive_examples, negative_examples, alphabet, implications=None):
        """
        Initialize RPNI with positive and negative examples, and implication constraints.
        :param positive_examples: Set of strings (positive examples).
        :param negative_examples: Set of strings (negative examples).
        :param alphabet: The alphabet of the automaton.
        :param implications: List of tuples (x, y) where if x is accepted, y must also be accepted.
        """
        self.positive_examples = positive_examples
        self.negative_examples = negative_examples
        self.alphabet = alphabet
        self.implications = implications if implications else []
        self.dfa = None

     
    

    def merge_states(self, state1, state2, dfa):
        """
        Attempts to merge two states in the DFA.
        :param state1: First state to merge.
        :param state2: Second state to merge.
        :param dfa: Current DFA structure.
        :return: True if the merge is consistent, False otherwise.
        """
        if state1 not in dfa or state2 not in dfa:
            # One of the states does not exist in the DFA
            return False

        # Create a copy of the DFA to perform the merge
        merged_dfa = {state: transitions.copy() for state, transitions in dfa.items()}

        # Redirect all transitions pointing to state2 to state1
        for state, transitions in merged_dfa.items():
            for symbol, target in transitions.items():
                if target == state2:
                    transitions[symbol] = state1

        # Merge transitions from state2 into state1
        for symbol, target in merged_dfa[state2].items():
            if symbol != "accepting":
                if symbol in merged_dfa[state1]:
                    # If a conflict occurs in the merged transitions, reject the merge
                    if merged_dfa[state1][symbol] != target:
                        return False
                else:
                    merged_dfa[state1][symbol] = target

        # Merge accepting status
        if "accepting" in merged_dfa[state2]:
            merged_dfa[state1]["accepting"] = True

        # Remove state2 from the DFA
        del merged_dfa[state2]

        # Check consistency with negative examples
        for neg_example in self.negative_examples:
            if self.is_example_accepted(neg_example, merged_dfa):
                # If any negative example is accepted, reject the merge
                return False
                
        # Check consistency with implication constraints
        for x, y in self.implications:
            if (self.is_example_accepted(x, merged_dfa) and 
                not self.is_example_accepted(y, merged_dfa)):
                # If x is accepted but y is not, reject the merge
                return False

        # Update the DFA with the merged structure
        dfa.clear()
        dfa.update(merged_dfa)
        return True
    
    def visualize_dfa(self, dfa, filename="dfa"):
        """
        Visualize the DFA using Graphviz.
        :param dfa: The DFA structure.
        :param filename: The output file name (without extension).
        """
        dot = Digraph(format="png")
        dot.attr(rankdir="LR")  # Left-to-right layout

        # Add states
        for state, transitions in dfa.items():
            if "accepting" in transitions:
                dot.node(state, shape="doublecircle")  # Accepting state
            else:
                dot.node(state, shape="circle")  # Regular state

        # Add transitions
        for state, transitions in dfa.items():
            for symbol, target in transitions.items():
                if symbol != "accepting":  # Ignore the "accepting" marker
                    dot.edge(state, target, label=symbol)

        # Render the graph to a file
        output_path = dot.render(filename)
        print(f"DFA visualization saved to {output_path}.")


    def is_example_accepted(self, example, dfa):
        """
        Checks if an example is accepted by the DFA.
        :param example: Input string to check.
        :param dfa: The DFA structure.
        :return: True if accepted, False otherwise.
        """
        current_state = 0  # Start from the initial numeric state (0)

        for symbol in example:
            # If the current state does not have a transition for the symbol, reject
            if current_state not in dfa or symbol not in dfa[current_state]:
                return False
            # Transition to the next state
            current_state = dfa[current_state][symbol]

        # Check if the final state is an accepting state
        return current_state in dfa and "accepting" in dfa[current_state]

    def solve_pos_ex(self, ex):
        """
        Solve the positive examples.
        """
        self.positive_examples.add(ex)

    def solve_neg_ex(self, ex):
        """
        Solve the negative examples.
        """
        self.negative_examples.add(ex)


    def build_pta(self):
        """
        Builds the Prefix Tree Acceptor (PTA) from positive examples,
        ensuring distinct paths for each example.
        States are numbered sequentially, starting with 0.
        """
        pta = {}
        state_counter = 0  # Numeric state counter
        state_map = {"": 0}  # Map from string-based state names to numeric states
        pta[0] = {}  # Initialize the initial state (numeric state 0)
        state_counter += 1

        for example in self.positive_examples:
            current_state = 0  # Start from the initial numeric state
            for symbol in example:
                next_state_name = str(current_state) + symbol
                if next_state_name not in state_map:
                    # Assign a new numeric state
                    state_map[next_state_name] = state_counter
                    pta[state_counter] = {}
                    state_counter += 1
                # Add transition to PTA
                next_state = state_map[next_state_name]
                pta[current_state][symbol] = next_state
                current_state = next_state

            # Mark the final state as accepting
            if "accepting" not in pta[current_state]:
                pta[current_state]["accepting"] = True

        return pta, state_map

    def run(self):
        """
        Runs the RPNI algorithm.
        Ensures states are represented as numbers, with the initial state as 0.
        """
        # Check for empty positive and negative examples
        if not self.positive_examples and not self.negative_examples:
            # Create a trivial DFA with one state (0) that accepts all inputs
            tab = {
                0: {symbol: 0 for symbol in self.alphabet}  # Loop on all inputs
            }
            ini = 0
            acc = {0}  # The single state is accepting
            self.dfa = DFAFromTab(self.alphabet, tab, ini, acc)
            return self.dfa

        # Step 1: Build the initial PTA
        pta, state_map = self.build_pta()

        # Step 2: Iteratively merge states in the PTA
        states = list(pta.keys())
        for i in range(len(states)):
            for j in range(i + 1, len(states)):
                if not self.merge_states(states[i], states[j], pta):
                    continue

        # Step 3: Finalize DFA
        ini = 0  # Initial state
        tab = {}
        acc = set()
        for state, transitions in pta.items():
            tab[state] = {}
            for symbol, target in transitions.items():
                if symbol != "accepting":
                    tab[state][symbol] = target
            if transitions.get("accepting"):
                acc.add(state)

        self.dfa = DFAFromTab(self.alphabet, tab, ini, acc)
        return self.dfa
    
class DFAFromTab(automata.NFA):
    def __init__(self, alphabet, tab, init, acc):
        super().__init__(alphabet)
        self.tab = tab
        self.init = init
        self.acc = acc
        self.reject_state = ""  # Define a reject state for undefined transitions

    def get_initial(self):
        yield self.init

    def get_succ(self, src, letter):
        # If the source state or letter is not defined, return no successors
        if src not in self.tab or letter not in self.tab[src]:
            return  # No valid transition, terminate
        else:
            yield self.tab[src][letter]

    def is_accepting(self, s):
        return s in self.acc

    
if __name__ == "__main__":
    # Example usage with implication constraints
    positive_examples = {"ab", "abab"}
    negative_examples = {"a", "ba", "aba"}
    alphabet = {"a", "b"}
    implications = [("abab", "ababab")]  # If "abab" is accepted, "ababab" must be accepted too

    rpni = RPNI(positive_examples, negative_examples, alphabet, implications)
    inferred_dfa = rpni.run()
    inferred_dfa.show_graphviz("rpni_with_implications")
    
    # Test the inferred DFA
    print(f"'ab' is accepted: {inferred_dfa.membership('ab')}")      # Should be True
    print(f"'abab' is accepted: {inferred_dfa.membership('abab')}")   # Should be True
    print(f"'a' is accepted: {inferred_dfa.membership('a')}")        # Should be False
    print(f"'ba' is accepted: {inferred_dfa.membership('ba')}")      # Should be False
    print(f"'aba' is accepted: {inferred_dfa.membership('aba')}")    # Should be False
    print(f"'ababab' is accepted: {inferred_dfa.membership('ababab')}") # Should be True due to implication