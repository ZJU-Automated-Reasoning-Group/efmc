# EFMC

SMT-based Software Model Checking

## 1. Introduction
EFMC is a toolkit for verifying program properties using SMT-based verification engines. It implements multiple approaches, such as template-based verification, property-directed reachability (PDR), Houdini, and k-induction. Each engine offers distinct advantages for different types of programs and properties.


### 1.1 Entrance of the Verifier

You can try the following command (in a virtual environemnt)
~~~~
pip install -e .
~~~~

Then, the `efmc` is a command-line tool, which supports programs specified in either CHC (Constrained Horn
Clauses) or SyGuS (Syntax-Guided Synthesis) format with pre- and
post-conditions.

~~~~
efmc -h
~~~~

Besides, the `efsmt` tool support solving the ``exists-forall`` SMT problems.
~~~~
efsmt -h
~~~~

## 2. The Main Verification Engines

Currently, the users can choose various verification engines

- Template-based (Constraint-based) Approach
- Property-Directed Reachability (PDR)
- K-Induction
- Quantifier Instantiation
- Houdini (NOT Stable)
- Abductive Inference (NOT Stable)

TBD: Download (or auto build) some third-party verifiers for comparison

### 2.1 Template-Based (Constraint-Based) Approach

This approach uses constraint solving to generate program
invariants based on predefined templates.

Related work:

- Linear Invariant Generation using Non-linear Constraint Solving, CAV 03
- Constraint-Based Linear-Relations Analysis, SAS'04
- Non-Linear Loop Invariant Generation using Gröbner Bases, POPL'04
- Program Analysis via Constraint Solving, PLDI'08
- Invgen: An Efficient Invariant Generator, CAV'09
- SMT-Based Array Invariant Generation, VMCAI'13

Currently, we do not apply Farkas' lemma, but use exists-forall SMT solving.

To run the engine, you may try two ways:

- Run `efmc`, which will use `efmc/engines/ef/ef_prover.py`.
- Run the test scripts, e.g., `efmc/tests/test_bvinerval.py`

Example:

~~~~
efmc --engine ef --template bv_interval --lang chc --file benchmarks/bv/2017.ASE_FIB/8bits_unsigned/fib_04.sl_8bits_unsigned.smt2

--engine: ef (the constraint-based approach)
          pdr (the PDR engine in Z3)
~~~~

If lang is not specified, efmc will guess the language based on the file extension.

### 2.2 Property-Directed Reachability (PDR)

Property-Directed Reachability (PDR), also known as IC3 (Incremental Construction of Inductive Clauses for Indubitable Correctness), is a formal verification technique that incrementally builds an inductive invariant to prove safety properties. PDR works by maintaining a sequence of over-approximations of reachable states and refining them through counterexample analysis.

In EFMC, we use the PDR engine inside Z3, named `Spacer`. To use it, you can run `efmc` with the `pdr` engine.

Example:

~~~~
efmc --engine pdr --lang chc --file file.smt2
~~~~

Related work:

- Efficient Implementation of Property Directed Reachability, FMCAD'12


### 2.3 K-Induction

K-induction is a powerful technique for proving safety properties of programs. It is based on the idea of proving that a
property holds for the base case and then proving that if the property holds for some state at a certain time step, it
also holds for the next state.

In EFMC, we have implemented a simple version of k-induction in `efmc/engines/kinduction`. To use it, you can
run `efmc` with the `kind` engine.

Example:

~~~~
efmc --engine kind --lang chc --file file.smt2
~~~~

Related work:

- Checking Safety Properties using Induction and a SAT-solver, FMCAD'00
- Software Verification using K-induction, SAS'11

#### 2.4 Abductive Inference
Abductive inference is a form of logical reasoning that starts with an observation and then seeks to find the (simplest) explanation. 

Related work:

- Inductive Invariant Generation via Abductive Inference, OOPSLA'13

#### Houdini

Houdini is an algorithm for inferring conjunctive invariants through a process of iterative weakening. It starts with the strongest possible conjunctive candidate and progressively removes conjuncts that are not inductive until it reaches a fixed point.

In EFMC, we have implemented Houdini in `efmc/engines/houdini`. To use it, you can run `efmc` with the `houdini` engine.

Example:

~~~~
efmc --engine houdini --lang chc --file file.smt2
~~~~

Related work:

- Houdini, an Annotation Assistant for ESC/Java, FME'01

#### Predicate Abstraction

## 3. Limitations and Future Work

### 3.1 Implementation of the Parsers

The parsers (and the transition system) are limited and not robust

- We assume there is only one loop, and there is one invariant (at loop header) to be generated.
    - No direct support for nested loops
    - No direct support for synthesizing multiple invariants at different locations of a lop
- We assume there are two matched groups of variables `x, y, z, ... x!, y!, z!,..` in the transition formula, where
  there primed variables end with `!`.
    - In practice, the `x!1` could be a constant
    - In some benchmarks, the primed variables could be ended with `'`
- There is no support for arrays (e.g., ALIA)

To extend the applicability, we need more frontends:

- Frontend for C programs (for more software verification benchmarks)
- Frontend for btor2 (for hardware model checking benchmarks)

### 3.2 Other Verification Engines

#### Abstract Interpretation with Symbolic Abstraction

#### Quantifier Instantiation

Solving the quantified formulas that characterize inductive invariants
directly (via different quantifier instantiation strategeis)

## Documentation

We release the doc here:  https://zju-automated-reasoning-group.github.io/efmc/

By deepwiki: https://deepwiki.com/ZJU-Automated-Reasoning-Group/efmc

A tutorial generated by AI:  https://code2tutorial.com/tutorial/214dae64-a7ac-49f6-b9fa-162fffabd51f/index.md

## Contributing

We welcome contributions to EFMC! Here's how you can contribute:

1. **Bug Reports**: If you find a bug, please open an issue on GitHub with a clear description of the problem, steps to reproduce, and your environment details.

2. **Feature Requests**: Have an idea for a new feature? Open an issue to discuss it.

3. **Code Contributions**: Want to add a new feature or fix a bug?
   - Fork the repository
   - Create a new branch for your feature
   - Add your code with appropriate tests
   - Submit a pull request

4. **Documentation**: Improvements to documentation are always welcome.

5. **Testing**: Help us test EFMC on different benchmarks and platforms.

## Contributors

Primary contributors to this project:

- rainoftime / cutelimination
- JasonJ2021
- WindOctober
- Zahrinas