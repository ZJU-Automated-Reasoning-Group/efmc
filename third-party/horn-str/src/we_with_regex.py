from itertools import product
import numpy as np
import copy
from typing import List, Tuple, Dict
import numpy as np
from itertools import product


def generate_one_hot_row_matrices(n: int) -> list[np.ndarray]:
    """
    Generate all n x n Boolean matrices where each row has exactly one '1'.
    """
    row_options = list(product([0, 1], repeat=n))
    valid_rows = [row for row in row_options if sum(row) == 1]

    matrices = []
    for rows in product(valid_rows, repeat=n):
        matrix = np.array(rows, dtype=int)
        matrices.append(matrix)
    return matrices


def nondet_choice(options):
    for option in options:
        yield option


def bool_mat_mult(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    n = a.shape[0]
    res = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                res[i][j] |= a[i][k] & b[k][j]
    return res


def find_all_boolean_matrix_solutions(x: np.ndarray, y: np.ndarray) -> list[np.ndarray]:
    """
    Return all matrices z such that:
    - y ∘ z = x (Boolean matrix multiplication)
    - each row in z has exactly one 1
    """
    n = x.shape[0]
    solutions = []
    for flat in product([0, 1], repeat=n * n):
        z = np.array(flat, dtype=int).reshape((n, n))
        if np.array_equal(bool_mat_mult(y, z), x) and np.all(np.sum(z, axis=1) == 1):
            solutions.append(z)
    return solutions


class MonoidHomomorphism:
    def __init__(self, alphabet: List[str], matrices: Dict[str, np.ndarray]):
        self.alphabet = alphabet
        self.matrices = matrices  # φ(a) = matrices[a]
        self.dimension = next(iter(matrices.values())).shape[0]

    def evaluate(self, word: str) -> np.ndarray:
        result = np.identity(self.dimension, dtype=int)
        for ch in word:
            if ch not in self.matrices:
                return np.zeros((self.dimension, self.dimension), dtype=int)
            result = BooleanAutomaton.bool_mat_mult(result, self.matrices[ch])
        return result


class BooleanAutomaton:
    def __init__(
        self,
        num_state: int,
        alphabet: List[str],
        transitions: Dict[str, np.ndarray],
        start: int | List[int],
        final: List[int],
    ):
        """
        transitions: Dict[symbol, matrix] of size (n x n)
        start: int or list[int] (multiple start states supported)
        """
        self.num_state = num_state
        self.alphabet = alphabet
        self.transitions = transitions  # symbol -> boolean matrix
        self.starts = [start] if isinstance(start, int) else start
        self.final = final

    def check_accept_matrix(self, mat: np.ndarray) -> bool:
        """Returns true iff ∃f. mat[start, f] = 1 for any start in self.starts"""
        return any(mat[s][f] == 1 for s in self.starts for f in self.final)

    def characteristic_matrix(self, word: str) -> np.ndarray:
        """
        Compute the characteristic matrix for a word w.
        M[i][j] = 1 iff the automaton accepts w from state i to state j.
        """
        n = self.num_state
        M = np.zeros((n, n), dtype=int)

        # For each pair (i, j), check if w takes i to j
        for i in range(n):
            for j in range(n):
                # Simulate a run from i to j
                aut = BooleanAutomaton(
                    num_state=self.num_state,
                    alphabet=self.alphabet,
                    transitions=self.transitions,
                    start=i,
                    final=[j],
                )
                if aut.accepts(word):
                    M[i][j] = 1
        return M

    def evaluate(self, word: str) -> np.ndarray:
        """Return the boolean matrix representing φ(word)"""
        n = self.num_state
        result = np.identity(n, dtype=int)  # identity matrix for boolean multiplication
        for ch in word:
            if ch not in self.transitions:
                return np.zeros((n, n), dtype=int)
            result = self.bool_mat_mult(result, self.transitions[ch])
        return result

    def accepts(self, word: str) -> bool:
        mat = self.evaluate(word)
        return any(mat[s][f] == 1 for s in self.starts for f in self.final)

    @staticmethod
    def bool_mat_mult(a: np.ndarray, b: np.ndarray) -> np.ndarray:
        """Boolean matrix multiplication (over ∨ and ∧)"""
        n = a.shape[0]
        res = np.zeros((n, n), dtype=int)
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    res[i][j] |= a[i][k] & b[k][j]
        return res

    def monoid_homomorphism(self) -> MonoidHomomorphism:
        """Returns the monoid homomorphism corresponding to this automaton"""
        return MonoidHomomorphism(self.alphabet, self.transitions)


def union_automata(automata: List[BooleanAutomaton]) -> BooleanAutomaton:
    if not automata:
        raise ValueError("No automata provided for union")

    alphabet = list(set().union(*(aut.alphabet for aut in automata)))
    total_states = 0
    transitions: Dict[str, np.ndarray | None] = {sym: None for sym in alphabet}
    new_starts = []
    new_finals = []

    for aut in automata:
        offset = total_states
        n = aut.num_state

        for sym in alphabet:
            old_matrix = aut.transitions.get(sym, np.zeros((n, n), dtype=int))
            padded = np.zeros((total_states + n, total_states + n), dtype=int)
            padded[offset : offset + n, offset : offset + n] = old_matrix

            if transitions[sym] is None:
                transitions[sym] = padded
            else:
                old_union = transitions[sym]
                m = old_union.shape[0]
                expanded = np.zeros((m + n, m + n), dtype=int)
                expanded[:m, :m] = old_union
                expanded[offset : offset + n, offset : offset + n] = old_matrix
                transitions[sym] = expanded

        new_starts.extend(s + offset for s in aut.starts)
        new_finals.extend(f + offset for f in aut.final)
        total_states += n

    # At this point all transitions[sym] are guaranteed to be np.ndarray
    return BooleanAutomaton(
        num_state=total_states,
        alphabet=alphabet,
        transitions=transitions,  # type: ignore
        start=new_starts,
        final=new_finals,
    )


def get_homomorphism_from_automaton(aut: BooleanAutomaton) -> MonoidHomomorphism:
    return MonoidHomomorphism(aut.alphabet, aut.transitions)


def check_word_satisfies_constraint(
    word: str, hom: MonoidHomomorphism, constraint_aut: BooleanAutomaton
) -> bool:
    mat = hom.evaluate(word)
    return constraint_aut.check_accept_matrix(mat)


def transformation_recursive_dfs(
    formula: str,
    f: Dict[str, np.ndarray],
    phi: MonoidHomomorphism,
    str_var: List[str],
    constants: List[str],
    trace: List[Tuple[str, str]] = None,
    visited: set = None,
    depth: int = 0,
    max_depth: int = 50,
) -> List[Tuple[str, str]]:
    if depth > max_depth:
        trace.append((formula, f"[max depth {max_depth} reached]"))
        return []

    if trace is None:
        trace = []
    if visited is None:
        visited = set()

    key = (formula, tuple(sorted((k, tuple(v.flatten())) for k, v in f.items())))
    if key in visited:
        return []
    visited.add(key)

    lhs, rhs = formula.split("=")
    if not lhs or not rhs:
        return []

    lhs_hd, rhs_hd = lhs[0], rhs[0]
    result: List[Tuple[str, str]] = []
    print(lhs_hd, rhs_hd, f, formula)

    def rec(new_formula: str, new_f: Dict[str, np.ndarray]) -> None:
        trace.append((formula, new_formula))
        result.append((formula, new_formula))
        result.extend(
            transformation_recursive_dfs(
                new_formula,
                new_f,
                phi,
                str_var,
                constants,
                trace,
                visited,
                depth + 1,
                max_depth,
            )
        )

    # rule P1
    if lhs_hd in str_var and np.array_equal(phi.evaluate(""), f[lhs_hd]):
        print("Rule P1 applied")
        new_formula = lhs[1:] + "=" + rhs[0] + rhs[1:].replace(lhs_hd, "")
        f1 = copy.deepcopy(f)
        del f1[lhs_hd]
        rec(new_formula, f1)

    elif rhs_hd in str_var and np.array_equal(phi.evaluate(""), f[rhs_hd]):
        print("Rule P1 applied")

        new_formula = lhs[0] + lhs[1:].replace(rhs_hd, "") + "=" + rhs[1:]
        f2 = copy.deepcopy(f)
        del f2[rhs_hd]
        rec(new_formula, f2)

    elif lhs_hd in str_var and rhs_hd in constants:
        phi_rhs = phi.evaluate(rhs_hd)
        for z in nondet_choice(find_all_boolean_matrix_solutions(f[lhs_hd], phi_rhs)):
            f_new = copy.deepcopy(f)
            f_new[lhs_hd] = z
            lhs_new = lhs[1:].replace(lhs_hd, rhs_hd + lhs_hd)
            rhs_new = rhs[1:].replace(lhs_hd, rhs_hd + lhs_hd)
            new_formula = lhs_hd + lhs_new + "=" + rhs_new
            rec(new_formula, f_new)

    elif lhs_hd in str_var and rhs_hd in str_var and lhs_hd == rhs_hd:
        new_formula = lhs[1:] + "=" + rhs[1:]
        f_new = copy.deepcopy(f)
        del f_new[lhs_hd]
        rec(new_formula, f_new)

    elif lhs_hd in str_var and rhs_hd in str_var:
        for z in nondet_choice(find_all_boolean_matrix_solutions(f[rhs_hd], f[lhs_hd])):
            fb = copy.deepcopy(f)
            fb[rhs_hd] = z
            form1 = (
                lhs[1:].replace(rhs_hd, lhs_hd + rhs_hd)
                + "="
                + rhs_hd
                + rhs[1:].replace(rhs_hd, lhs_hd + rhs_hd)
            )
            rec(form1, fb)

        for z in nondet_choice(find_all_boolean_matrix_solutions(f[lhs_hd], f[lhs_hd])):
            fa = copy.deepcopy(f)
            fa[lhs_hd] = z
            form2 = (
                lhs_hd
                + lhs[1:].replace(lhs_hd, rhs_hd + lhs_hd)
                + "="
                + rhs[1:].replace(lhs_hd, rhs_hd + lhs_hd)
            )
            rec(form2, fa)

    elif lhs_hd in constants and rhs_hd in constants and lhs_hd == rhs_hd:
        new_formula = lhs[1:] + "=" + rhs[1:]
        rec(new_formula, copy.deepcopy(f))

    elif lhs_hd in constants and rhs_hd in str_var:
        phi_lhs = phi.evaluate(lhs_hd)
        for z in nondet_choice(find_all_boolean_matrix_solutions(f[rhs_hd], phi_lhs)):
            f_new = copy.deepcopy(f)
            f_new[rhs_hd] = z
            lhs_new = lhs[1:].replace(rhs_hd, lhs_hd + rhs_hd)
            rhs_new = rhs[1:].replace(rhs_hd, lhs_hd + rhs_hd)
            new_formula = lhs_new + "=" + rhs_hd + rhs_new
            rec(new_formula, f_new)

    return result


# Print trace as a tree


def print_trace_as_tree(trace: List[Tuple[str, str]]) -> Tuple[bool, str]:
    res = ""
    from collections import defaultdict

    tree = defaultdict(list)
    for parent, child in trace:
        tree[parent].append(child)

    def dfs(node: str, depth: int = 0, visited: set = None) -> bool:
        nonlocal res  # Fixes the UnboundLocalError
        if visited is None:
            visited = set()
        if node in visited:
            return False
        visited.add(node)
        res += "  " * depth + f"- {node}\n"
        found_eq = node == "="
        for child in tree.get(node, []):
            found_eq |= dfs(child, depth + 1, visited)
        return found_eq

    roots = {p for p, _ in trace} - {c for _, c in trace}
    if not roots:
        roots = [trace[0][0]] if trace else []

    found = False
    for root in roots:
        found |= dfs(root)

    return found, res


def transform_into_chc_LR(formula, steps):
    res = f"""(set-logic HORN)
(declare-fun Acc (String String) Bool)"""
    res += f"""; init
(assert
  (forall ((L String) (R String))
    (=>
        (and
            (= L \"{formula.split('=')[0]}\")
            (= R \"{formula.split('=')[1]}\")
        )
      (Acc L R)
    )
  )
)"""
    res += f"""
; Bad zone
(assert
  (forall ((L String) (R String))
    (=>
      (and
        (= L "")
        (= R "")
        (Acc L R)
      )
      false
    )
  )
)
"""
    for pre, post in steps:
        res += f"""
(assert
  (forall ((L String) (R String) (L1 String) (R1 String))
    (=>
        (and
          (Acc L R)
          (= L \"{pre.split('=')[0]}\")
          (= R \"{pre.split('=')[1]}\")
          (= L1 \"{post.split('=')[0]}\")
          (= R1 \"{post.split('=')[1]}\")
        )
      (Acc L1 R1)
    )
  )
)"""
    res += "\n\n(check-sat)"
    return res


def transform_into_chc_monadic(formula, steps):
    res = f"""(set-logic HORN)
(declare-fun Acc (String) Bool)"""
    res += f"""; init
(assert
  (forall ((X String))
    (=>
      (= X \"{formula}\")
      (Acc X)
    )
  )
)"""
    res += f"""
; Bad zone
(assert
  (forall ((X String))
    (=>
      (and
        (= X "=")
        (Acc X)
      )
      false
    )
  )
)
"""
    for pre, post in steps:
        res += f"""
(assert
  (forall ((X String) (Y String))
    (=>
        (and
          (Acc X)
          (= X \"{pre}\")
          (= Y \"{post}\")
        )
      (Acc Y)
    )
  )
)"""
    res += "\n\n(check-sat)"
    return res


def test1():
    trans_x = {
        "a": np.array(
            [
                [1]
            ]
        )
    } 
    trans_y = {
        "a": np.array(
            [
                [0,1,0,0],
                [0,1,0,0],
                [0,0,0,1],
                [0,0,0,1]
            ]
        ),
        "b": np.array(
            [
                [0,0,0,1],
                [0,0,1,0],
                [0,0,1,0],
                [0,0,0,1]
            ])
    }

    trans_z = {
        "b": np.array(
            [
                [1]
            ]
        )
    } 

    auto_x = BooleanAutomaton(1, ["a"], trans_x, 0, [0])
    auto_y = BooleanAutomaton(4, ["a", "b"], trans_y, 0, [2])
    auto_z = BooleanAutomaton(1, ["b"], trans_z, 0, [0])
    A = union_automata([auto_x, auto_y, auto_z])
    print(A.num_state)
    phi = get_homomorphism_from_automaton(A)


    formula = "ZYX=XXZ"
    str_var = ["X", "Y", "Z"]
    constants = ["a", "b"]
    
    for xi, fx in enumerate(generate_one_hot_row_matrices(6)):
        f = {"X": fx}
        for yi, fy in enumerate(generate_one_hot_row_matrices(6)):
            f["Y"] = fy
            for zi, fz in enumerate(generate_one_hot_row_matrices(6)):
                f["Z"] = fz
                print(f"Testing with matrices X = {xi}, Y={yi}, Z={zi}")
                trace = []
                transformation_recursive_dfs(
                    formula, f, phi, str_var, constants, trace=trace, max_depth=1
                )
                found_eq, trace = print_trace_as_tree(trace)
                print(xi+yi+zi, trace)


def test2():
    trans_x = {
        "a": np.array(
            [
                [1]
            ]
        ),
        "b": np.array(
            [
                [1]
            ]
        )
    } 
      
    auto_x = BooleanAutomaton(1, ["a", "b"], trans_x, 0, [0])
    A = union_automata([auto_x])
    print(A.num_state)
    phi = get_homomorphism_from_automaton(A)


    formula = "XXbX=XaXX"
    str_var = ["X"]
    constants = ["a", "b"]
    
    for xi, fx in enumerate(generate_one_hot_row_matrices(1)):
        f = {"X": fx}
        trace = []
        transformation_recursive_dfs(
            formula, f, phi, str_var, constants, trace=trace, max_depth=1
        )
        found_eq, trace = print_trace_as_tree(trace)
        print(xi, trace)

def test3():
    '''xxyy=zz ∧ x ∈ aΣ∗ ∧y ∈ bΣ∗'''
    trans_x = {
        "a": np.array(
            [
                [0,1,0],
                [0,1,0],
                [0,0,1]
            ]
        ),
        "b": np.array(
            [
                [0,0,1],
                [0,1,0],
                [0,0,1]
            ]
        )
    } 
    trans_y = {
        "b": np.array(
            [
                [0,1,0],
                [0,1,0],
                [0,0,1]
            ]
        ),
        "a": np.array(
            [
                [0,0,1],
                [0,1,0],
                [0,0,1]
            ]
        )
    } 
    trans_Z = {
        "a": np.array(
            [
                [1]
            ]
        ),
        "b": np.array(
            [
                [1]
            ]
        )
    } 
      
    auto_z = BooleanAutomaton(1, ["a", "b"], trans_Z, 0, [0])

      
    auto_x = BooleanAutomaton(3, ["a", "b"], trans_x, 0, [1])
    auto_y = BooleanAutomaton(3, ["a", "b"], trans_y, 0, [1])

    A = union_automata([auto_x, auto_y, auto_z])
    print(A.num_state)
    phi = get_homomorphism_from_automaton(A)


    formula = "XXYY=ZZ"
    str_var = ["X", "Y", "Z"]
    constants = ["a", "b"]
    
    for xi, fx in enumerate(generate_one_hot_row_matrices(A.num_state)):
        f = {"X": fx}
        for yi, fy in enumerate(generate_one_hot_row_matrices(A.num_state)):
            f["Y"] = fy
            for zi, fz in enumerate(generate_one_hot_row_matrices(A.num_state)):
                f["Z"] = fz
                print(f"Testing with matrices X = {xi}, Y={yi}, Z={zi}")
                trace = []
                transformation_recursive_dfs(
                    formula, f, phi, str_var, constants, trace=trace, max_depth=1
                )
                found_eq, trace = print_trace_as_tree(trace)
                print(xi+yi+zi, trace)


if __name__ == "__main__":
    test3()
