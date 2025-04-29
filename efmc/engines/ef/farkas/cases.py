def demo_cases():
    # Test Case 1: Simple counter program (x >= 0)
    counter_chc = """
    (declare-var x Int)
    (declare-var x_next Int)
    (rule (=> (= x 0) inv(x)))
    (rule (=> (and inv(x) (= x_next (+ x 1))) inv(x_next)))
    (rule (=> (inv x) (>= x 0)))
    """

    # Test Case 2: Two-variable counter (x <= y)
    two_var_counter = """
    (declare-var x Int)
    (declare-var y Int)
    (declare-var x_next Int)
    (declare-var y_next Int)
    (rule (=> (and (= x 0) (= y 10)) inv(x y)))
    (rule (=> (and inv(x y) (= x_next (+ x 1)) (= y_next y)) inv(x_next y_next)))
    (rule (=> (inv x y) (<= x y)))
    """

    # Test Case 3: Difference bounds (x - y <= 5)
    difference_bounds = """
    (declare-var x Int)
    (declare-var y Int)
    (declare-var x_next Int)
    (declare-var y_next Int)
    (rule (=> (and (= x y) (= y 0)) inv(x y)))
    (rule (=> (and inv(x y) (= x_next (+ x 1)) (= y_next y)) inv(x_next y_next)))
    (rule (=> (inv x y) (<= (- x y) 5)))
    """

    # Test Case 4: Simple loop with multiple paths
    multi_path_loop = """
    (declare-var x Int)
    (declare-var x_next Int)
    (rule (=> (= x 0) inv(x)))
    (rule (=> (and inv(x) (< x 10) (= x_next (+ x 1))) inv(x_next)))
    (rule (=> (and inv(x) (>= x 10) (= x_next x)) inv(x_next)))
    (rule (=> (inv x) (>= x 0)))
    """

    # Test Case 5: Mutual recursion
    mutual_recursion = """
    (declare-var x Int)
    (declare-var y Int)
    (declare-var x_next Int)
    (declare-var y_next Int)
    (rule (=> (and (= x 0) (= y 0)) inv1(x y)))
    (rule (=> (and inv1(x y) (= x_next (+ x 1)) (= y_next y)) inv2(x_next y_next)))
    (rule (=> (and inv2(x y) (= y_next (+ y 1)) (= x_next x)) inv1(x_next y_next)))
    (rule (=> (inv1 x y) (>= (+ x y) 0)))
    """

    # Test Case 6: Bounded sum
    bounded_sum = """
    (declare-var x Int)
    (declare-var y Int)
    (declare-var s Int)
    (declare-var x_next Int)
    (declare-var y_next Int)
    (declare-var s_next Int)
    (rule (=> (and (= x 0) (= y 0) (= s 0)) inv(x y s)))
    (rule (=> (and inv(x y s) 
                  (< x 10)
                  (= x_next (+ x 1))
                  (= y_next (+ y 2))
                  (= s_next (+ s x_next))) 
              inv(x_next y_next s_next)))
    (rule (=> (inv x y s) (<= s (* x y))))
    """

    # Test Case 7: Array bounds (simplified)
    array_bounds = """
    (declare-var i Int)
    (declare-var n Int)
    (declare-var i_next Int)
    (rule (=> (and (= i 0) (>= n 0)) inv(i n)))
    (rule (=> (and inv(i n) (< i n) (= i_next (+ i 1))) inv(i_next n)))
    (rule (=> (inv i n) (>= n i)))
    """

    # Test Case 8: Multiple invariants
    multiple_invariants = """
    (declare-var x Int)
    (declare-var y Int)
    (declare-var x_next Int)
    (declare-var y_next Int)
    (rule (=> (and (= x 0) (= y 0)) inv(x y)))
    (rule (=> (and inv(x y) 
                  (= x_next (+ x 1))
                  (= y_next (+ y 2))) 
              inv(x_next y_next)))
    (rule (=> (inv x y) (>= y 0)))
    (rule (=> (inv x y) (>= x 0)))
    (rule (=> (inv x y) (= y (* 2 x))))
    """

    test_cases = [
        ("Counter Program", counter_chc),
        ("Two-Variable Counter", two_var_counter),
        ("Difference Bounds", difference_bounds),
        ("Multi-Path Loop", multi_path_loop),
        ("Mutual Recursion", mutual_recursion),
        ("Bounded Sum", bounded_sum),
        ("Array Bounds", array_bounds),
        ("Multiple Invariants", multiple_invariants)
    ]

    return test_cases
