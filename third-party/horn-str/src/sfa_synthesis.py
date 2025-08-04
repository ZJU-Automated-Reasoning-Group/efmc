import json
import os
import subprocess
import uuid

import config
import re
import z3
from typing import Dict, Set, List, Tuple, Optional

class SFA(object):
    """
    Symbolic Finite Automaton (SFA) representation.
    Can read automata from DOT files with support for symbolic transitions.
    """

    def __init__(self, filename: str = None):
        """
        Initialize an SFA, optionally loading from a DOT file.
        
        Args:
            filename: Path to a DOT file containing an automaton
        """
        # Initialize data structures
        self._states = set()
        self._accept_states = set()
        self._initial_state = None
        self._transitions = dict()
        self.filename = filename
        
        if filename:
            self.load_from_dot(filename)
    
    def unicode_to_int(self, uni_str):
        if uni_str.startswith(r'\u'):
            return int(uni_str[2:], 16)
        else:
            return ord(uni_str)
    
    def load_from_dot(self, filename: str):
        """
        Load an automaton from a DOT file.
        
        Args:
            filename: Path to DOT file
        """
        try:
            with open(filename, 'r') as f:
                dot_content = f.read()
            
            # Extract states
            state_pattern = r'(\d+)\s*\[.*?\]'
            for match in re.finditer(state_pattern, dot_content):
                state = int(match.group(1))
                self._states.add(state)
            
            # Find initial state
            init_pattern = r'XX(\d+)\s*->\s*(\d+)'
            init_matches = re.findall(init_pattern, dot_content)
            if init_matches:
                self._initial_state = int(init_matches[0][1])
            
            # Extract transitions
            trans_pattern = r'(\d+)\s*->\s*(\d+)\s*\[label="([^"]+)"\]'
            for match in re.finditer(trans_pattern, dot_content):
                src = int(match.group(1))
                dst = int(match.group(2))
                label = match.group(3)
                # Handle Unicode character ranges
                x = re.findall(r'(\\u[0-9a-zA-Z]{4}-\\u[0-9a-zA-Z]{4})', label[1:-1])
                for l in x:
                    lhs = l.split('-')[0]
                    rhs = l.split('-')[1]
                    # print(lhs, ord(lhs))
                    constraint = f"CHAR_RANGE({self.unicode_to_int(lhs)},{self.unicode_to_int(rhs)})"
                    edge = (src, dst)
                    if edge in self._transitions:
                        self._transitions[edge].append(constraint)
                    else:
                        self._transitions[edge] = [constraint]
                # Handle single character in brackets like [t]
                # elif re.match(r'\[(.*?)\]', label):
                #     match = re.match(r'\[(.*?)\]', label)
                #     if match:
                #         char = match.group(1)
                #         if len(char) == 1:
                #             char_code = ord(char)
                #             constraint = f"CHAR_RANGE({char_code},{char_code})"
                #             edge = (src, dst)
                #             if edge in self._transitions:
                #                 self._transitions[edge].append(constraint)
                #             else:
                #                 self._transitions[edge] = [constraint]
                            
            # Extract accept states
            accept_pattern = r'(\d+)\s*\[.*?peripheries=2.*?\]'
            for match in re.finditer(accept_pattern, dot_content):
                state = int(match.group(1))
                self._accept_states.add(state)
            
        except Exception as e:
            print(f"Error parsing DOT file: {e}")
    
        
    def show(self, title="SFA"):
        """
        Display the SFA using Graphviz.
        
        Args:
            title: Title for the visualization
        """
        # dot_file = os.path.join(config.get_default_tmp_dir(), "resultAutomaton.dot")
        dot_file = self.filename
        # print(f"Showing SFA from DOT file: {dot_file}")
        try:
            # Check if the file exists
            if not os.path.exists(dot_file):
                print(f"Warning: DOT file not found at {dot_file}")
                return
                
            # Use graphviz to display the automaton
            output_png = os.path.join(config.get_default_tmp_dir(), f"{title}.png")
            
            # Run dot command to convert dot file to PNG
            cmd = ["dot", "-Tpng", dot_file, "-o", output_png]
            try:
                subprocess.run(cmd, check=True)
                
                # Try to display the image if running in a GUI environment
                if os.name == 'posix':  # Linux/Unix
                    subprocess.run(["xdg-open", output_png], stderr=subprocess.DEVNULL)
                elif os.name == 'nt':  # Windows
                    subprocess.run(["start", output_png], shell=True)
                elif os.name == 'darwin':  # macOS
                    subprocess.run(["open", output_png])
                    
            except subprocess.CalledProcessError:
                print("Failed to render the automaton. Is Graphviz installed?")
                print("You can view the DOT file directly at:", dot_file)
                
        except Exception as e:
            print(f"Error showing SFA: {e}")
            

    
    def accepts(self, word: str) -> bool:
        """
        Check if the automaton accepts a given word.
        
        Args:
            word: The input string to check
            
        Returns:
            True if the automaton accepts the word, False otherwise
        """
        if self._initial_state is None:
            return False
            
        current_state = self._initial_state
        
        # Process each character in the word
        for char in word:
            char_code = ord(char)
            next_state = None
            # Check all possible transitions
            for (src, dst), conditions in self._transitions.items():
                
                if src == current_state:
                    for condition in conditions:
                        # For character ranges
                        if condition.startswith("CHAR_RANGE"):
                            match = re.match(r"CHAR_RANGE\((\d+),(\d+)\)", condition)
                            if match:
                                start = int(match.group(1))
                                end = int(match.group(2))
                                if start <= char_code <= end:
                                    next_state = dst
                                    break
                            
                if next_state:
                    break
                    
            if next_state is None:
                return False  # No valid transition found
                
            current_state = next_state
        # Check if final state is accepting
        return current_state in self._accept_states
    
    def complement(self):
        """
        Return a new SFA that accepts the complement language:
        same structure but with accept‐states flipped.
        Note: for truly correct complement of a partial automaton you
        should add a sink state and complete the transitions.
        """
        comp = SFA()  
        # copy states & initial
        comp._states = self._states.copy()
        comp._initial_state = self._initial_state
        # flip accepting set
        comp._accept_states = self._states.difference(self._accept_states)
        # deep‐copy transitions
        comp._transitions = {
            (src, dst): conds.copy()
            for (src, dst), conds in self._transitions.items()
        }
        return comp
    
    def to_smt(self, var_name="X", automaton_name="value_0"):
        """
        Convert the SFA to an SMT formula using re.from_automaton syntax.
        
        Args:
            var_name: The variable name to use in the assertion
            automaton_name: The name to give the automaton
        
        Returns:
            An SMT-LIB string assertion for membership in the automaton
        """
        # Start building the automaton string
        automaton_str = f"automaton {automaton_name} {{"
        
        # Add initial state
        if self._initial_state is not None:
            automaton_str += f"init s{self._initial_state}; "
        else:
            return "(assert false)"  # No initial state, automaton rejects everything
        
        # Add transitions
        for (src, dst), conditions in self._transitions.items():
            for condition in conditions:
                if condition.startswith("CHAR_RANGE"):
                    match = re.match(r"CHAR_RANGE\((\d+),(\d+)\)", condition)
                    if match:
                        start = int(match.group(1))
                        end = int(match.group(2))
                        automaton_str += f"s{src} -> s{dst} [{start}, {end}]; "
        
        # Add accepting states
        if self._accept_states:
            automaton_str += f"accepting "
            # print(f"accepting {self._accept_states}")
            automaton_str += ", ".join([f"s{state}" for state in self._accept_states])
            automaton_str += "; "
        else:
            automaton_str += f"accepting none; "
        
        # Close the automaton definition
        automaton_str += "};"
        
        # Wrap in the SMT assertion
        smt_formula = f'(assert (str.in.re {var_name} (re.from_automaton "{automaton_str}")))'
        
        return smt_formula
    
    def get_nb_states(self):
        """
        Get the number of states in the SFA.
        
        Returns:
            The number of states
        """
        return len(self._states)

    def __str__(self):
        """String representation of the SFA"""
        res = "Symbolic Finite Automaton:\n"
        res += f"States: {self._states}\n"
        res += f"Initial State: {self._initial_state}\n"
        res += f"Accept States: {self._accept_states}\n"
        res += "Transitions:\n"
        for (src, dst), conditions in self._transitions.items():
            for condition in conditions:
                res += f"{src} --[{condition}]--> {dst}\n"
        return res
    
    def export_as_regex(self):
        """
        Export the SFA as a regular expression pattern (if possible).
        For simple automata with character ranges.
        
        Returns:
            A string containing a regex pattern or None if not possible
        """
        # Only handle simple cases for now
        if len(self._states) == 1 and self._initial_state in self._accept_states:
            # Check if there's a self-loop with the full Unicode range
            for (src, dst), conditions in self._transitions.items():
                for cond in conditions:
                    if cond == "CHAR_RANGE(0,65535)" and src == dst == self._initial_state:
                        return ".*"  # Matches any string including empty string
        
        # More complex regex generation would go here
        return None


class SFAPassiveLearnerBase(object):

    # def __init__(self):
        #z3.parse_smt2_string('(declare-const x Int) (assert (> x 0)) (assert (< x 10))')

        #x, y = z3.Reals("x0 x1")
        #z3.parse_smt2_string('(assert (and (= 1.0 x0) (= 1.0 x1)))', decls={'x0': x, 'x1': y})

    def __init__(self, positive_examples, negative_examples, inductive_examples, setting=None):
        """
        Initialize RPNI with positive and negative examples.
        :param positive_examples: Set of strings (positive examples).
        :param negative_examples: Set of strings (negative examples).
        :param alphabet: The alphabet of the automaton.
        """
        self.positive_examples = positive_examples
        self.negative_examples = negative_examples
        self.inductive_examples = inductive_examples
        self.setting = setting
        self.iteration = 0
        # self.alphabet = alphabet
        # self.dfa = None
        # pass

    def run(self):
        """
        Runs the passive learning from samples
        """
        sfa = None

        # create dir if it does not exist
        os.makedirs(config.get_default_tmp_dir(), exist_ok=True)
        samples = {}
        samples['pos'] = list(self.positive_examples)
        samples['neg'] = list(self.negative_examples)
        samples['ind'] = list(self.inductive_examples)

        unique_samples_filename = config.get_default_tmp_dir() + os.sep + "samples_{}_{}.json".format(self.iteration, uuid.uuid4().hex)
        result_name = config.get_default_tmp_dir() + os.sep + "resultAutomaton_{}_".format(self.iteration) + uuid.uuid4().hex

        with open(unique_samples_filename, "w") as pos_neg:

            json.dump(samples, pos_neg)
            pos_neg.close()

            java = config.get_default_solver_from_config("java")
            learner_jar = config.get_default_solver_from_config("sfa-learner-jar")

            #CMD = java + ["-Xss20000k", "-Xmx200m" "-jar"] + learner_jar + ["--theory", "CharComparison"]
            CMD = java + ["-jar"] + learner_jar + ["--theory", "CharComparison"]
            # add strategy
            if self.setting:
                if "edsm" in self.setting:
                    CMD += ["--strategy", "edsm"]
                elif "rpni" in self.setting:
                    CMD += ["--strategy", "rpni"]
                else: # default
                    CMD += ["--strategy", "edsm"]
            else:
                CMD += ["--strategy", "edsm"]

            CMD +=["-i", pos_neg.name, "-o", result_name, "-format", "json"]

            res = subprocess.run(CMD)
            if res.returncode == 5:
                print("Positive: ", self.positive_examples)
                print("Negative: ", self.negative_examples)
                raise RuntimeError("Exit code: {}. Most likely cause: Positive/Negative sets are not disjoint.".format(res.returncode))
            if res.returncode != 0:
                raise RuntimeError("Running Learner exited with errorcode {}!".format(res.returncode))

            sfa = SFA(result_name + ".dot")

        # maybe add debug flag for removing this:
        os.remove(result_name + ".dot")
        os.remove(unique_samples_filename)
        self.iteration +=1

        return sfa

    def solve_pos_ex(self, pos_ex):
        """
        Solve the positive examples
        :param pos_ex: The positive example to solve
        """
        self.positive_examples.append(pos_ex)
    
    def solve_ind_ex(self, ind_ex):
        """
        Solve the positive examples
        :param pos_ex: The positive example to solve
        """
        self.inductive_examples.append(ind_ex)

    def solve_neg_ex(self, neg_ex):
        """
        Solve the negative examples
        :param neg_ex: The negative example to solve
        """
        self.negative_examples.append(neg_ex)


class SFAPassiveLearnerOverApprox(SFAPassiveLearnerBase):
    def __init__(self, positive_examples, negative_examples, inductive_examples, setting=None):
        super().__init__(positive_examples, negative_examples, inductive_examples, setting)

    def solve_ind_ex(self, ind_ex):
        if ind_ex[0] in self.positive_examples:
            if ind_ex[1] not in self.negative_examples:
                self.solve_pos_ex(ind_ex[1])
        elif ind_ex[1] in self.negative_examples:
            if ind_ex[0] not in self.positive_examples:
                self.solve_neg_ex(ind_ex[0])
        elif (ind_ex[0] not in self.negative_examples) and (ind_ex[1] not in self.negative_examples):
            self.solve_pos_ex(ind_ex[0])
            self.solve_pos_ex(ind_ex[1])

        elif (ind_ex[0] in self.positive_examples) and (ind_ex[1] in self.negative_examples):
            self.negative_examples.remove(ind_ex[0])
            self.negative_examples.remove(ind_ex[1])

            self.positive_examples.append(ind_ex[0])
            self.positive_examples.append(ind_ex[1])
        

        if not (set(self.positive_examples) & set(self.negative_examples) == set()):
            raise Exception



if __name__ == "__main__":
    # sfa = SFA("tmp/resultAutomaton.dot")
    # print(sfa)
    # # You can customize the variable name and automaton name
    # custom_formula = sfa.to_smt(var_name="x", automaton_name="my_automaton")
    # print(custom_formula)
    sfa = SFA("/Users/sword/work/string-chc-lib/tmp/resultAutomaton_7_6dea589c93f74cfeaf1969afa54ec25a.dot")
    # print(sfa._transitions)
    # learner = SFAPassiveLearnerUnicode({'t'}, {""})
    # sfa = learner.run()
    # print(sfa.accepts("t"))
    # print(sfa.to_smt())
    # sfa.show("123")