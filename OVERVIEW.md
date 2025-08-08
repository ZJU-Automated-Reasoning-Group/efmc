# EFMC Overview

## Verification Engines

EFMC implements multiple verification approaches, each offering distinct advantages for different types of programs and properties:

### Template-Based (Constraint-Based) Approach

This approach uses constraint solving to generate program invariants based on predefined templates.

**Related work:**
- Linear Invariant Generation using Non-linear Constraint Solving, CAV 03
- Constraint-Based Linear-Relations Analysis, SAS'04
- Non-Linear Loop Invariant Generation using Gröbner Bases, POPL'04
- Program Analysis via Constraint Solving, PLDI'08
- Invgen: An Efficient Invariant Generator, CAV'09
- SMT-Based Array Invariant Generation, VMCAI'13

Currently, we do not apply Farkas' lemma, but use exists-forall SMT solving.

**Usage:**
```bash
efmc --engine ef --template bv_interval --lang chc --file benchmarks/bv/2017.ASE_FIB/8bits_unsigned/fib_04.sl_8bits_unsigned.smt2
```

**Engine options:**
- `ef` (the constraint-based approach)
- `pdr` (the PDR engine in Z3)

### Property-Directed Reachability (PDR)

Property-Directed Reachability (PDR), also known as IC3 (Incremental Construction of Inductive Clauses for Indubitable Correctness), is a formal verification technique that incrementally builds an inductive invariant to prove safety properties. PDR works by maintaining a sequence of over-approximations of reachable states and refining them through counterexample analysis.

In EFMC, we use the PDR engine inside Z3, named `Spacer`.

**Usage:**
```bash
efmc --engine pdr --lang chc --file file.smt2
```

**Related work:**
- Efficient Implementation of Property Directed Reachability, FMCAD'12

### K-Induction

K-induction is a powerful technique for proving safety properties of programs. It is based on the idea of proving that a property holds for the base case and then proving that if the property holds for some state at a certain time step, it also holds for the next state.

In EFMC, we have implemented a simple version of k-induction in `efmc/engines/kinduction`.

**Usage:**
```bash
efmc --engine kind --lang chc --file file.smt2
```

**Related work:**
- Checking Safety Properties using Induction and a SAT-solver, FMCAD'00
- Software Verification using K-induction, SAS'11

### Abductive Inference

Abductive inference is a form of logical reasoning that starts with an observation and then seeks to find the (simplest) explanation.

**Related work:**
- Inductive Invariant Generation via Abductive Inference, OOPSLA'13

### Houdini

Houdini is an algorithm for inferring conjunctive invariants through a process of iterative weakening. It starts with the strongest possible conjunctive candidate and progressively removes conjuncts that are not inductive until it reaches a fixed point.

In EFMC, we have implemented Houdini in `efmc/engines/houdini`.

**Usage:**
```bash
efmc --engine houdini --lang chc --file file.smt2
```

**Related work:**
- Houdini, an Annotation Assistant for ESC/Java, FME'01

### Predicate Abstraction

Predicate abstraction is a technique for creating finite-state abstractions of infinite-state systems by using predicates to partition the state space.

## Current Limitations

### Implementation of the Parsers

The parsers (and the transition system) are limited and not robust:

- We assume there is only one loop, and there is one invariant (at loop header) to be generated.
  - No direct support for nested loops
  - No direct support for synthesizing multiple invariants at different locations of a loop
- We assume there are two matched groups of variables `x, y, z, ... x!, y!, z!,..` in the transition formula, where the primed variables end with `!`.
  - In practice, the `x!1` could be a constant
  - In some benchmarks, the primed variables could be ended with `'`
- There is no support for arrays (e.g., ALIA)

To extend the applicability, we need more frontends:
- Frontend for C programs (for more software verification benchmarks)
- Frontend for btor2 (for hardware model checking benchmarks)

### Other Verification Engines

#### Abstract Interpretation with Symbolic Abstraction

#### Quantifier Instantiation

Solving the quantified formulas that characterize inductive invariants directly (via different quantifier instantiation strategies)

## Future Work

TBD: Download (or auto build) some third-party verifiers for comparison
