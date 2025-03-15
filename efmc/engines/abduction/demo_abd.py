"""
Test module for the Abductive Inference-based Invariant Generation.

This module provides comprehensive test cases for the AbductionProver implementation,
comparing results with K-induction verification. It includes various transition systems
ranging from simple to complex scenarios to verify the prover's effectiveness.

Each test case is documented with:
- System description and properties
- Expected verification results
- Theoretical invariants (when known)
"""

import logging
import time
from dataclasses import dataclass
from typing import List, Tuple, Optional

import z3

from efmc.engines.abduction.abduction_prover import AbductionProver
from efmc.engines.kinduction.kind_prover import KInductionProver
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


@dataclass
class TestCase:
    """Represents a single test case for verification."""
    name: str
    system: TransitionSystem
    expected_safe: bool
    description: str
    theoretical_invariant: Optional[str] = None


class VerificationResults:
    """Stores and compares verification results from different provers."""

    def __init__(self, name: str, system: TransitionSystem):
        self.name = name
        self.system = system
        self.kind_result = None  # Can be True (safe), False (unsafe), or None (unknown)
        self.kind_is_unknown = False  # Flag to indicate if the result is unknown
        self.abduction_result = None
        self.abduction_invariant = None
        self.execution_time = 0.0

    def __str__(self) -> str:
        if self.kind_is_unknown:
            kind_status = "unknown"
        else:
            kind_status = "safe" if self.kind_result else "unsafe"
        abd_status = "safe" if self.abduction_result else "unsafe"

        result = f"\nTest Case: {self.name}\n"
        result += f"{'=' * 50}\n"
        result += f"K-induction result: {kind_status}\n"
        result += f"Abduction result: {abd_status}\n"
        result += f"Execution time: {self.execution_time:.2f}s\n"

        if self.abduction_invariant is not None:
            result += f"Found invariant: {self.abduction_invariant}\n"

        return result


class TransitionSystemFactory:
    """Factory class for creating test transition systems."""

    @staticmethod
    def create_simple_loop() -> TestCase:
        """Create a simple loop system where y = 2x."""
        x, y = z3.Ints('x y')
        xp, yp = z3.Ints("x! y!")

        init = z3.And(x == 0, y == 0)
        trans = z3.And(xp == x + 1, yp == y + 2)
        post = y <= 2 * x

        system = TransitionSystem(
            variables=[x, y],
            prime_variables=[xp, yp],
            init=init,
            trans=trans,
            post=post
        )

        return TestCase(
            name="Simple Loop",
            system=system,
            expected_safe=True,
            description="Simple loop maintaining y = 2x relationship",
            theoretical_invariant="y = 2x"
        )

    @staticmethod
    def create_faulty_system() -> TestCase:
        """Create a system that violates its safety property."""
        a, b = z3.Ints('a b')
        ap, bp = z3.Ints("a! b!")

        init = z3.And(a == 0, b == 0)
        trans = z3.And(ap == a + 1, bp == b + 1)
        post = b < a

        system = TransitionSystem(
            variables=[a, b],
            prime_variables=[ap, bp],
            init=init,
            trans=trans,
            post=post
        )

        return TestCase(
            name="Faulty System",
            system=system,
            expected_safe=False,
            description="System with parallel increments violating b < a",
            theoretical_invariant="None (unsafe)"
        )

    @staticmethod
    def create_bounded_loop() -> TestCase:
        """Create a system with a bounded loop counter."""
        i = z3.Int('i')
        ip = z3.Int("i!")

        init = i == 0
        trans = z3.If(i < 10, ip == i + 1, ip == i)
        post = i <= 10

        system = TransitionSystem(
            variables=[i],
            prime_variables=[ip],
            init=init,
            trans=trans,
            post=post
        )

        return TestCase(
            name="Bounded Loop",
            system=system,
            expected_safe=True,
            description="Counter system with upper bound of 10",
            theoretical_invariant="0 <= i <= 10"
        )

    @staticmethod
    def create_dependent_variables() -> TestCase:
        """Create a system with dependent variable relationships."""
        n, m = z3.Ints('n m')
        np, mp = z3.Ints("n! m!")

        init = z3.And(n == 2, m == 1)
        trans = z3.And(np == n + 1, mp == n)
        post = m <= n / 2

        system = TransitionSystem(
            variables=[n, m],
            prime_variables=[np, mp],
            init=init,
            trans=trans,
            post=post
        )

        return TestCase(
            name="Dependent Variables",
            system=system,
            expected_safe=False,
            description="System with m tracking n-1, violating m <= n/2",
            theoretical_invariant="None (unsafe)"
        )


class VerificationTester:
    """Manages the execution and reporting of verification tests."""

    def __init__(self, k_induction_bound: int = 20):
        self.k_bound = k_induction_bound
        self.results: List[VerificationResults] = []

    def verify_system(self, test_case: TestCase) -> VerificationResults:
        """Verify a system using both K-induction and Abduction approaches."""
        result = VerificationResults(test_case.name, test_case.system)

        # K-induction verification
        kind_prover = KInductionProver(test_case.system)
        kind_prover.use_aux_invariant = False
        kind_result = kind_prover.solve(k=self.k_bound)

        # Check if the result is unknown
        if kind_result.is_unknown:
            result.kind_is_unknown = True
            result.kind_result = None
        else:
            result.kind_result = kind_result.is_safe

        # Abduction verification
        start_time = time.time()
        abduction_prover = AbductionProver(test_case.system)

        try:
            verification_result = abduction_prover.solve()
            result.abduction_result = verification_result.is_safe
            result.abduction_invariant = verification_result.invariant
        except Exception as e:
            logger.error(f"Error during abduction verification: {e}")
            result.abduction_result = False

        result.execution_time = time.time() - start_time

        self.results.append(result)
        return result

    def run_all_tests(self) -> None:
        """Run all predefined test cases."""
        test_cases = [
            TransitionSystemFactory.create_simple_loop(),
            TransitionSystemFactory.create_faulty_system(),
            TransitionSystemFactory.create_bounded_loop(),
            TransitionSystemFactory.create_dependent_variables()
        ]

        logger.info("Starting verification tests...")
        for test_case in test_cases:
            logger.info(f"\nVerifying {test_case.name}")
            result = self.verify_system(test_case)

            # Verify results match expectations
            assert result.abduction_result == test_case.expected_safe, \
                f"Unexpected result for {test_case.name}: " \
                f"expected {'safe' if test_case.expected_safe else 'unsafe'}, " \
                f"got {'safe' if result.abduction_result else 'unsafe'}"

            print(result)

    def generate_report(self) -> str:
        """Generate a summary report of all test results."""
        report = "\nVerification Test Summary\n"
        report += "=" * 50 + "\n"

        total_tests = len(self.results)
        successful_tests = sum(1 for r, tc in zip(self.results, [
            TransitionSystemFactory.create_simple_loop(),
            TransitionSystemFactory.create_faulty_system(),
            TransitionSystemFactory.create_bounded_loop(),
            TransitionSystemFactory.create_dependent_variables()
        ]) if r.abduction_result == tc.expected_safe)

        report += f"Total tests run: {total_tests}\n"
        report += f"Successful abduction verifications: {successful_tests}\n"
        report += f"Abduction accuracy: {successful_tests / total_tests:.1%}\n"

        # Count how many k-induction results were unknown
        unknown_kind_results = sum(1 for r in self.results if r.kind_is_unknown)
        if unknown_kind_results > 0:
            report += f"K-induction unknown results: {unknown_kind_results}/{total_tests}\n"

        total_time = sum(r.execution_time for r in self.results)
        report += f"Total execution time: {total_time:.2f}s\n"
        report += f"Average time per test: {total_time / total_tests:.2f}s\n"

        return report


def main():
    """Main entry point for running verification tests."""
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s'
    )

    try:
        tester = VerificationTester()
        tester.run_all_tests()
        print(tester.generate_report())

    except Exception as e:
        logger.error(f"Test execution failed: {e}", exc_info=True)
        raise


if __name__ == "__main__":
    main()
