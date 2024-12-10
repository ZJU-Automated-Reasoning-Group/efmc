
# EFMC
SMT-based Software Model Checking

## 1. Introduction
EFMC is a toolkit for verifying program properties using SMT-based verification engines. 
It implements multiple approaches including template-based verification, 
property-directed reachability (PDR), and k-induction. 
Each engine offers distinct advantages for different types of programs 
and properties.

### 1.1 Entrance of the Verifier

The main verification interface is through prover.py, which supports programs specified in either CHC (Constrained Horn Clauses) or 
SyGuS (Syntax-Guided Synthesis) format with pre- and 
post-conditions.

~~~~
prover.py
~~~~

### 1.2 Other Useful Files

The following file can be used for solving exists-forall problems
over bit-vectors.

~~~~
cegis.py
~~~~


## 2. The Main Verification Engines

Currently, the users can choose three verification engines
- Template-based (Constraint-based) Approach
- Property-Directed Reachability (PDR)
- K-Induction

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
- Run `prover.py`, which will use `efmc/engines/ef/ef_prover.py`.
- Run the test scripts, e.g., `efmc/tests/test_bvinerval.py`

Example:
~~~~
python3 prover.py --engine efsmt --template bv_interval --lang chc --file benchmarks/bv/2017.ASE_FIB/8bits_unsigned/fib_04.sl_8bits_unsigned.smt2

--engine: efsmt (the constraint-based approach)
          pdr (the PDR engine in Z3)
~~~~

### 2.2 Property-Directed Reachability (PDR)

In EFMC, we use the PDR engine inside Z3, named `Spacer`. To use it, you can run `prover.py` with the `pdr` engine. 


Example:
~~~~
python3 prover.py --engine pdr --lang chc --file file.smt2
~~~~


### 2.3 K-Induction

K-induction is a powerful technique for proving safety properties of programs. It is based on the idea of proving that a property holds for the base case  and then proving that if the property holds for some state at a certain time step, it also holds for the next state.

In EFMC, we have implemented a simple version of k-induction in `efmc/engines/kinduction`. To use it, you can run `prover.py` with the `kind` engine.

Example:
~~~~
python3 prover.py --engine kind --lang chc --file file.smt2
~~~~

Related work:
- Checking 

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

### 3.2 Other Verification Engines

#### Abstract Interpretation

#### Abductive Inference

Related work:
- Inductive Invariant Generation via Abductive Inference, OOPSLA 13

TODO: not implemented yet

#### Quantifier Instantiation

Solving the quantified formulas that characterize inductive invariants
directly (via different quantifier instantiation strategeis)

## TBD

- Frontend (for C programs)
- Download (or auto build) some verifiers for comparison 


For more topics, please refer to ``docs/todo.md``

## Contributors

Primary contributors to this project:
- rainoftime / cutelimination
- JasonJ2021
- WindOctober
