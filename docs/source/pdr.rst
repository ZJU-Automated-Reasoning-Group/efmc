Property Directed Reachability (PDR)
===================================

The Property Directed Reachability (PDR) module uses the IC3/PDR algorithm inside Z3's Constrained Horn Clause (CHC) engine. PDR is a powerful technique for safety verification that incrementally builds inductive invariants.

======================
Overview
======================

Property Directed Reachability (PDR), also known as IC3 (Incremental Construction of Inductive Clauses for Indubitable Correctness), is a SAT/SMT-based model checking algorithm that incrementally constructs inductive invariants to prove safety properties.


======================
Algorithm
======================

The PDR prover formulates the verification problem as Constrained Horn Clauses (CHC) and uses Z3's CHC engine to solve it:

1. **Problem Formulation**: Convert the verification problem into CHC:
   - Initiation: ∀x. init(x) → inv(x)
   - Inductiveness: ∀x,x'. inv(x) ∧ trans(x,x') → inv(x')
   - Safety: ∀x. inv(x) → post(x)

2. **CHC Solving**: Use Z3's CHC engine to find a satisfying assignment for the invariant function

3. **Result Interpretation**: Interpret the solver's result:
   - **SAT**: System is safe, invariant found
   - **UNSAT**: System is unsafe or unknown


======================
Usage
======================

The PDR prover can be used as follows:

.. code-block:: python

    from efmc.engines.pdr import PDRProver
    from efmc.sts import TransitionSystem
    
    # Create transition system
    sts = TransitionSystem(...)
    
    # Create PDR prover
    prover = PDRProver(sts)
    prover.set_verbose(True)  # Enable verbose output
    
    # Solve the verification problem
    result = prover.solve(timeout=60)
    
    if result.is_safe:
        print("System is safe")
        print(f"Invariant: {result.invariant}")
    else:
        print("System is unsafe or unknown")



======================
Example
======================

Consider a simple counter program:

.. code-block:: c

    int x = 0;
    while (x < 10) {
        x = x + 1;
    }
    assert(x == 10);

The PDR prover would:
1. Formulate CHC problem with invariant function inv(x)
2. Add constraints:
   - ∀x. (x = 0) → inv(x)  // Initiation
   - ∀x,x'. inv(x) ∧ (x < 10 ∧ x' = x + 1) → inv(x')  // Inductiveness
   - ∀x. inv(x) → (x ≥ 0 ∧ x ≤ 10)  // Safety
3. Use Z3's CHC engine to find inv(x) = (x ≥ 0 ∧ x ≤ 10)
4. Verify that the invariant implies the safety property



======================
References
======================

.. [1] A. R. Bradley, "SAT-based model checking without unrolling," in VMCAI, 2011.
