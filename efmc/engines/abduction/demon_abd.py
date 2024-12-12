from efmc.engines.abduction.abduction_prover import *
from efmc.engines.kinduction.kind_prover import KInductionProver


def check_with_kind(sts):
    print("Running one test...")
    pp = KInductionProver(sts)
    pp.use_aux_invariant = False
    res = pp.solve(k=20)
    return res

def demo_abduction_prover():
    """Demonstrates the usage of the AbductionProver with test cases."""

    def create_simple_loop() -> TransitionSystem:
        """Create a simple loop system where y = 2x."""
        x, y = z3.Ints('x y')
        xp, yp = z3.Ints("x! y!")

        init = z3.And(x == 0, y == 0)
        trans = z3.And(xp == x + 1, yp == y + 2)
        post = y <= 2 * x  # Invariant y = 2x

        return TransitionSystem(
            variables=[x, y],
            prime_variables=[xp, yp],
            init=init,
            trans=trans,
            post=post
        )

    def create_faulty_system() -> TransitionSystem:
        """Create a system that violates the safety property."""
        a, b = z3.Ints('a b')
        ap, bp = z3.Ints("a! b!")

        init = z3.And(a == 0, b == 0)
        trans = z3.And(ap == a + 1, bp == b + 1)
        post = b < a  # Safety property b < a, which is never true in transitions

        return TransitionSystem(
            variables=[a, b],
            prime_variables=[ap, bp],
            init=init,
            trans=trans,
            post=post
        )

    def create_counter_system() -> TransitionSystem:
        """Create a system with a possible counterexample."""
        i = z3.Int('i')
        j = z3.Int('j')
        ip, jp = z3.Ints("i! j!")

        init = z3.And(i == 0, j == 0)
        trans = z3.And(ip == i + 1, jp == j + 1)
        post = j <= i  # Safety property j <= i, which holds initially but can be violated

        return TransitionSystem(
            variables=[i, j],
            prime_variables=[ip, jp],
            init=init,
            trans=trans,
            post=post
        )

    # Additional Test Cases
    def create_mutual_increment_system() -> TransitionSystem:
        """Create a system where two variables are incremented together."""
        x, y = z3.Ints('x y')
        xp, yp = z3.Ints("x! y!")

        init = z3.And(x == 0, y == 0)
        trans = z3.And(xp == x + 1, yp == y + 1)
        post = y <= 2 * x  # Maintain y does not exceed twice x

        return TransitionSystem(
            variables=[x, y],
            prime_variables=[xp, yp],
            init=init,
            trans=trans,
            post=post
        )

    def create_decrementing_system() -> TransitionSystem:
        """Create a system that decrements a variable, potentially making it negative."""
        x = z3.Int('x')
        xp = z3.Int("x!")

        init = x == 5
        trans = xp == x - 1
        post = x >= 0  # Safety property: x remains non-negative

        return TransitionSystem(
            variables=[x],
            prime_variables=[xp],
            init=init,
            trans=trans,
            post=post
        )

    def create_two_variable_relationship() -> TransitionSystem:
        """Create a system where a and b maintain a >= 2 * b."""
        a, b = z3.Ints('a b')
        ap, bp = z3.Ints("a! b!")

        init = z3.And(a == 4, b == 1)
        trans = z3.And(ap == a + 2, bp == b + 1)
        post = a >= 2 * b  # Maintain a >= 2 * b

        return TransitionSystem(
            variables=[a, b],
            prime_variables=[ap, bp],
            init=init,
            trans=trans,
            post=post
        )

    def create_dependent_variables_system() -> TransitionSystem:
        """Create a system where m = n - 1, violating m <= n / 2."""
        n, m = z3.Ints('n m')
        np, mp = z3.Ints("n! m!")

        init = z3.And(n == 2, m == 1)
        trans = z3.And(np == n + 1, mp == n)  # m = n (will violate m <= n / 2)
        post = m <= n / 2  # Safety property

        return TransitionSystem(
            variables=[n, m],
            prime_variables=[np, mp],
            init=init,
            trans=trans,
            post=m <= (n / 2)
        )

    def create_bounded_loop_system() -> TransitionSystem:
        """Create a system where i counts from 0 to 10."""
        i = z3.Int('i')
        ip = z3.Int("i!")

        init = i == 0
        trans = z3.If(
            i < 10,
            ip == i + 1,
            ip == i  # Loop stops incrementing after 10
        )
        post = i <= 10  # Safety property: i does not exceed 10

        return TransitionSystem(
            variables=[i],
            prime_variables=[ip],
            init=init,
            trans=trans,
            post=i <= 10
        )

    # Define test cases
    systems = [
        # Existing Test Cases
        ("Simple Loop", create_simple_loop(), True),
        ("Faulty System", create_faulty_system(), False),
        # ("Counter System", create_counter_system(), False),

        # Additional Test Cases
        ("Mutual Increment System", create_mutual_increment_system(), True),
        ("Decrementing System", create_decrementing_system(), False),
        ("Two-Variable Relationship", create_two_variable_relationship(), True),
        ("Dependent Variables System", create_dependent_variables_system(), False),
        ("Bounded Loop System", create_bounded_loop_system(), True)
    ]

    for name, system, expected_safe in systems:
        print(f"\nTesting {name}:")
        kind_res = check_with_kind(system)
        print("K induction result: ", kind_res)

        prover = AbductionProver(system)
        safe, inv = prover.verify()

        print(f"System is {'safe' if safe else 'unsafe'}")
        print(f"Expected: {'safe' if expected_safe else 'unsafe'}")
        if safe:
            print(f"Inductive invariant: {inv}")
        else:
            print("No inductive invariant found.")

        assert safe == expected_safe, f"Incorrect result for {name}"


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    demo_abduction_prover()
