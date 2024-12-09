import re
from dataclasses import dataclass
from typing import List, Dict
import z3


def demo_parsing():
    # Test case with explicit transitions
    chc_input = """
    (declare-var x Int)
    (declare-var x_next Int)
    (rule (=> (= x 0) inv(x)))
    (rule (=> (and inv(x) (= x_next (+ x 1))) inv(x_next)))
    (rule (=> (inv x) (>= x 0)))
    """

    synthesizer = InvariantSynthesizer()
    synthesizer.parse_chc(chc_input)

    print("Variables:", synthesizer.variables)
    print("\nTransitions:")
    for t in synthesizer.transitions:
        print(f"Pre vars: {[v.name for v in t.pre_vars]}")
        print(f"Post vars: {[v.name for v in t.post_vars]}")
        print(f"Constraint: {t.constraint}")
        print("---")

    # Test case with more complex transitions
    complex_chc = """
    (declare-var x Int)
    (declare-var y Int)
    (declare-var x_next Int)
    (declare-var y_next Int)
    (rule (=> (and (= x 0) (= y 0)) inv(x y)))
    (rule (=> (and inv(x y) 
                  (= x_next (+ x 1))
                  (= y_next (+ y 2))) 
              inv(x_next y_next)))
    (rule (=> (inv x y) (and (>= y 0) (>= x 0))))
    """

    print("\nTesting complex CHC:")
    synthesizer = InvariantSynthesizer()
    synthesizer.parse_chc(complex_chc)

    print("Variables:", synthesizer.variables)
    print("\nTransitions:")
    for t in synthesizer.transitions:
        print(f"Pre vars: {[v.name for v in t.pre_vars]}")
        print(f"Post vars: {[v.name for v in t.post_vars]}")
        print(f"Constraint: {t.constraint}")
        print("---")


if __name__ == "__main__":
    demo_parsing()
    # demo_cases()
