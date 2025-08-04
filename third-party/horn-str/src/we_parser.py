from z3 import *
from regex import Z3Builder, RegexParser
import numpy as np
from typing import Dict, List
from typing import List, Tuple, Dict

 
# put this near the top:
class NielsenSolutionFound(Exception):
    """
    Raised as soon as we discover a 'solved' equation (empty side or lhs==rhs).
    Carries the full trace of formulas visited.
    """
    def __init__(self, trace: List[str]):
        super().__init__("solution found")
        self.trace = trace

def nielsen_transformation_single_equation(
    formula: str,
    str_var: list[str],
    constants: list[str],
    visited: set[str] = None,
    depth: int = 0,
    max_depth: int = 20,
    trace: List[str] = None,
    found_solution: List[bool] = None
) -> list[tuple[str, str, tuple[str,str]]]:
    # Initialize shared state
    if visited        is None: visited        = set()
    if trace          is None: trace          = []
    if found_solution is None: found_solution = [False]

    # If we've already found lhs==rhs somewhere below, bail out immediately
    if found_solution[0]:
        return []

    # Record this formula in the trace
    trace.append(formula)

    # Depth‐limit guard
    if depth >= max_depth:
        return []

    # Split sides
    lhs, rhs = formula.split("=")

    # Only treat exact equality as a solution
    if lhs == rhs:
        found_solution[0] = True
        return []

    # Otherwise, if either side is empty but not equal, continue exploring
    if not lhs or not rhs:
        # no flag, but nothing to transform
        return []

    # Avoid cycles
    if formula in visited:
        return []
    visited.add(formula)

    lhs_hd, rhs_hd = lhs[0], rhs[0]
    result: list[tuple[str, str, tuple[str,str]]] = []

    def recurse(newf: str):
        if not found_solution[0]:
            result.extend(nielsen_transformation_single_equation(
                newf, str_var, constants,
                visited, depth+1, max_depth,
                trace, found_solution
            ))

    # --- P1, P3, P4 on lhs-var ---
    if lhs_hd in str_var:
        # P1: erase X prefix
        new_l = lhs[1:].replace(lhs_hd, "")
        new_r = rhs_hd + rhs[1:].replace(lhs_hd, "")
        step = (formula, f"{new_l}={new_r}", (lhs_hd, ""))
        result.append(step)
        recurse(step[1])
        if found_solution[0]: return result

        # P3: if rhs_hd is constant, push it past X
        if rhs_hd in constants:
            p3_l = lhs[1:].replace(lhs_hd, f"{rhs_hd}{lhs_hd}")
            p3_r = rhs[1:].replace(lhs_hd, f"{rhs_hd}{lhs_hd}")
            step = (formula, f"{lhs_hd}{p3_l}={p3_r}", (lhs_hd, f"{rhs_hd}{lhs_hd}"))
            result.append(step)
            recurse(step[1])
            if found_solution[0]: return result
        else:
            # P4a: same head
            if lhs_hd == rhs_hd:
                stripped = f"{lhs[1:]}={rhs[1:]}"
                step = (formula, stripped, (lhs_hd, rhs_hd))
                result.append(step)
                recurse(stripped)
                if found_solution[0]: return result
            # P4b: cross‐shuffle
            else:
                f1 = f"{lhs[1:].replace(rhs_hd, lhs_hd+rhs_hd)}={rhs_hd}{rhs[1:].replace(rhs_hd, lhs_hd+rhs_hd)}"
                f2 = f"{lhs_hd}{lhs[1:].replace(lhs_hd, rhs_hd+lhs_hd)}={rhs[1:].replace(lhs_hd, rhs_hd+lhs_hd)}"
                step1 = (formula, f1, (rhs_hd, lhs_hd+rhs_hd))
                step2 = (formula, f2, (lhs_hd, rhs_hd+lhs_hd))
                result.extend([step1, step2])
                recurse(f1)
                if found_solution[0]: return result
                recurse(f2)
                if found_solution[0]: return result

    # --- P2 on rhs-var ---
    elif rhs_hd in str_var:
        # erase Y prefix on RHS
        new_l = lhs[0] + lhs[1:].replace(rhs_hd, "")
        new_r = rhs[1:].replace(rhs_hd, "")
        step = (formula, f"{new_l}={new_r}", (rhs_hd, ""))
        result.append(step)
        recurse(step[1])
        if found_solution[0]: return result

        # push L prefix past Y
        p2_l = lhs[1:].replace(rhs_hd, lhs_hd+rhs_hd)
        p2_r = rhs[1:].replace(rhs_hd, lhs_hd+rhs_hd)
        step = (formula, f"{p2_l}={rhs_hd}{p2_r}", (rhs_hd, lhs_hd+rhs_hd))
        result.append(step)
        recurse(step[1])
        if found_solution[0]: return result

    # --- P5: common‐head cancellation when neither side starts with a variable ---
    else:
        if lhs_hd == rhs_hd:
            stripped = f"{lhs[1:]}={rhs[1:]}"
            step = (formula, stripped, (lhs_hd, rhs_hd))
            result.append(step)
            recurse(stripped)
            if found_solution[0]: return result

    return result



from typing import List, Tuple
from collections import defaultdict

def print_trace_as_tree(
    trace: List[Tuple[str, str, Tuple[str, str]]]
) -> Tuple[bool, str, int]:
    """
    trace: list of (parent, child, (var, repl))
    returns (found_eq_flag, pretty_str, max_depth)
    """
    res = ""
    max_depth = 0

    # build a tree: parent -> list of (child, (var,repl))
    tree: Dict[str, List[Tuple[str, Tuple[str,str]]]] = defaultdict(list)
    for parent, child, upd in trace:
        tree[parent].append((child, upd))

    def dfs(node: str, depth: int = 0, visited: set[str] = None) -> bool:
        nonlocal res, max_depth
        if visited is None:
            visited = set()
        if node in visited:
            # already printed this node on the current path
            return False
        visited.add(node)

        # record depth
        max_depth = max(max_depth, depth)
        # print this node
        # res += "  " * depth + f"- {depth}: {node}\n"

        # check goal
        if node.split("=")[0] == node.split("=")[1]:
            found_eq = True
        else:
            found_eq = False

        # for each outgoing edge, print the update then recurse
        for child, (var, repl) in tree.get(node, []):
            # annotate the substitution on the next line
            res += "  " * (depth + 2) + f"{depth + 1}: {child} [{var} → {repr(repl)}]\n"

            found_eq |= dfs(child, depth + 1, visited)

        return found_eq

    # find roots (parents that never appear as children)
    parents  = {p for p, _, _ in trace}
    children = {c for _, c, _ in trace}
    roots = list(parents - children)
    if not roots and trace:
        roots = [trace[0][0]]

    found_any = False
    for root in roots:
        res +=  f"- : {root}\n"
        found_any |= dfs(root)

    return found_any, res, max_depth



def check_constant_matches_regex(constant: str, regex_str: str) -> bool:
    builder = Z3Builder()
    parser = RegexParser(builder)
    z3_expr = parser.parse(regex_str)
    s = Solver()
    s.add(InRe(StringVal(constant), z3_expr))
    return s.check() == sat


def check_regexes_intersect(regex1: str, regex2: str) -> bool:
    builder = Z3Builder()
    parser = RegexParser(builder)
    re1 = parser.parse(regex1)
    re2 = parser.parse(regex2)
    s = Solver()
    x = String("x")
    s.add(InRe(x, Intersect(re1, re2)))
    s.add(x != StringVal(""))
    return s.check() == sat

  

def substitute_in_all_equations(old: str, new: str, system: List[str]) -> List[str]:
    return [eq.replace(old, new) for eq in system]

def find_solutions_single_eq(
    formula: str,
    str_var: List[str],
    constants: List[str],
    max_depth: int = 20,
) -> List[List[Tuple[str,str]]]:
    """
    Returns a list of substitution-chains.
    Each chain is a list of (var, replacement) steps which,
    when applied in order to `formula`, eventually produces
    lhs == rhs or an empty side.
    """
    solutions: List[List[Tuple[str,str]]] = []

    def dfs(
        current: str,
        depth: int,
        visited: set[str],
        chain: List[Tuple[str,str]],
    ):
        if depth > max_depth:
            return
        if current in visited:
            return
        visited.add(current)

        lhs, rhs = current.split("=")
        # base‐case
        if not lhs or not rhs or lhs == rhs:
            solutions.append(chain.copy())
            return

        hdL, hdR = lhs[0], rhs[0]
        # generate the same (formula, new_formula, (var,repl)) triples
        steps = nielsen_transformation_single_equation(
            current, str_var, constants
        )
        for (_, newf, (var, repl)) in steps:
            # record the substitution
            chain.append((var, repl))
            dfs(newf, depth + 1, set(visited), chain)
            chain.pop()

    dfs(formula, 0, set(), [])
    return solutions


# ----------------------------------------------------------------
# 2) apply a whole chain of substitutions to every equation
# ----------------------------------------------------------------
def apply_chain_to_system(
    chain: List[Tuple[str,str]],
    system: List[str]
) -> List[str]:
    out = system[:]
    for (var, repl) in chain:
        out = [ eq.replace(var, repl) for eq in out ]
    return out


# ----------------------------------------------------------------
# 3) recursive multi‐equation solver
# ----------------------------------------------------------------
def nielsen_transformation_multi_equation(
    system: List[str],
    str_var: List[str],
    constants: List[str],
    max_depth: int = 20,
) -> List[List[Tuple[str,str]]]:
    """
    Returns a list of full substitution‐chains which solve the entire system.
    Each chain is a concatenation of the per‐equation chains, in order.
    """
    # if there's no equations left, empty chain is a valid “solution”
    if not system:
        return [[]]

    first, *rest = system
    all_sols: List[List[Tuple[str,str]]] = []

    # 1) find all ways to solve the first equation
    single_solutions = find_solutions_single_eq(first, str_var, constants, max_depth)

    for chain in single_solutions:
        # 2) apply that chain to the rest of the system
        new_rest = apply_chain_to_system(chain, rest)
        # 3) recurse on the tail
        tail_sols = solve_word_equations(new_rest, str_var, constants, max_depth)
        # 4) prepend our chain to each tail‐solution
        for tail_chain in tail_sols:
            all_sols.append(chain + tail_chain)

    return all_sols


def print_trace_as_tree_multi(trace: List[Tuple[List[str], List[str]]]) -> Tuple[bool, str]:
    from collections import defaultdict
    res = ""
    max_depth = 0

    # Normalize list-of-equations to a single string to use as a key
    def normalize(eqs: List[str]) -> str:
        return "&".join(sorted(eqs))

    tree = defaultdict(list)
    for parent, child in trace:
        parent_key = normalize(parent)
        child_key = normalize(child)
        tree[parent_key].append(child_key)

    def dfs(node: str, depth: int = 0, visited: set = None) -> bool:
        nonlocal res, max_depth
        if visited is None:
            visited = set()
        if node in visited:
            return False
        visited.add(node)
        max_depth = max(max_depth, depth)
        res += "  " * depth + f"- {node}\n"
        found_goal = node == "" or node == "="  # you may customize this
        for child in tree.get(node, []):
            found_goal |= dfs(child, depth + 1, visited)
        return found_goal

    roots = {normalize(p) for p, _ in trace} - {normalize(c) for _, c in trace}
    if not roots:
        roots = [normalize(trace[0][0])] if trace else []

    found = False
    for root in roots:
        found |= dfs(root)

    return found, res, max_depth



def transform_into_chc_LR(str_var, formula, steps):
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


def transform_into_chc_monadic(str_var, formula, steps):
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
    formula = "X0011Y=11Z00"
    str_var = ["X", "Y", "Z"]
    constants = ["1", "0"]

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, depth = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(f"Max depth: {depth}")
    print(trace)

def test2():
    formula = "abXcY=YcXba"
    str_var = ["X", "Y"]
    constants = ["a", "b", "c"]

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(trace)

def test3():
    try:
        formula = "X=Xa"
        str_var = ["X"]
        constants = ["a", "b"]
        steps = nielsen_transformation_single_equation(formula, str_var, constants, max_depth=3)
        f, trace, d = print_trace_as_tree(steps)
        print(trace)
    except NielsenSolutionFound as e:
        print("Found a solution/counterexample!")
        print("Trace:")
        for f in e.trace:
            print("  ", f)

def test4():
    formula = "ABCDE=DECBA"
    str_var = ["A", "B", "C", "D", "E"]
    constants = []

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(trace)

def test5():
    formula = "XZ=ZY"
    str_var = ["X", "Y", "Z"]
    constants = []

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(trace)

def test6():
    formula = "XZZ=ZZY"
    str_var = ["X", "Y", "Z"]
    constants = []

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(trace)

def test7():
    formula = "XXYY=ZZ"
    str_var = ["X", "Y", "Z"]
    constants = []

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(trace)

def test8():
    formula = "aX=Xa"
    str_var = ["X"]
    constants = ["a"]

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(trace)


def test9():
    formula = "XZY=YTX"
    str_var = ["X", "Y", "Z", "T"]
    constants = []

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f} depth: {d}")
    print(trace)
    


def test10():
    formula = "X=Xa"
    str_var = ["X", "Y"]
    constants = ["a"]

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(trace)

 
    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(trace)

def test11():
    formula = "XY=YX"
    str_var = ["X", "Y"]
    constants = []

    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    # print(f"Found goal: {f}")
    # print(trace)

 
    steps = nielsen_transformation_single_equation(formula, str_var, constants)
    f, trace, d = print_trace_as_tree(steps)
    print(f"Found goal: {f}")
    print(trace)

def test_multi():
    equations = ["X=ABC", "C=dD", "B=aE", "XX=AABBCC"]
    str_var = ["X", "A", "B", "C", "D", "E"]
    constants = ["a", "d"]
    steps = nielsen_transformation_multi_equation(equations, str_var, constants)
    f, trace, d = print_trace_as_tree_multi(steps)
    print(f"Found goal: {f}") 
    print(f"Max depth: {d}")
    # print(trace)

def test_multi1():
    equations = ["XY=UV", "YX=VU"]
    str_var = ["X", "Y", "U", "V"]
    constants = []
    steps = nielsen_transformation_multi_equation(equations, str_var, constants)
    f, trace, d = print_trace_as_tree_multi(steps)
    print(f"Found goal: {f}") 
    print(trace)
    print(f"Max depth: {d}")

def test_multi2():
    equations = ["XXYYY=ZZ", "X=aX", "Y=bY"]
    str_var = ["X", "Y", "Z", "A", "B"]
    constants = ["a", "b"]
    steps = nielsen_transformation_multi_equation(equations, str_var, constants)
    f, trace, d = print_trace_as_tree_multi(steps)
    print(f"Found goal: {f}") 
    print(trace)
    print(f"Max depth: {d}")

def test_multi3():
    equations = ["XZ=ZY", "XZZ=ZZX"]
    str_var = ["X", "Y", "Z"]
    constants = []
    steps = nielsen_transformation_single_equation(equations, str_var, constants)
    f, trace, d = print_trace_as_tree_multi(steps)
    print(f"Found goal: {f}") 
    print(trace)
    print(f"Max depth: {d}")

def test_reduction():
    formula = "Xab=abX"
    str_var = ["X", "Y", "Z"]
    constants = ["a", "b"]
    steps = nielsen_transformation_single_equation(formula, str_var, constants,max_depth=12)
    # print("no trivial solution found within depth") 

    
    f, trace, d = print_trace_as_tree(steps)
    # print(f"Found goal: {f}")
    print(trace)
if __name__ == "__main__":
    # print(123)
    test9()
