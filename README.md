
# EFMC

## 1. Introduction
This toolkit provides a set of engines for verifying properties of programs. The engines are based on different approaches, such as template-based (constraint-based) approach, property-directed reachability (PDR), and K-induction. 
Each engine has its own strengths and weaknesses, and can be used for different types of programs and properties. In this README, we provide a brief overview of each engine and how to use it.

### 1.1 Entrance of the Verifier

To verify a program specified via CHC or SyGuS 
format (annotated with pre- and post conditions),
you may use the following file
~~~~
prover.py
~~~~

### 1.2 Other Useful Files

The following file can be used for solving exists-forlal problems
over bit-vectors.
~~~~
cegis.py
~~~~


## 2. The Main Engines

Currently, the users can choose three verification engiens
- Template-based (Constraint-based) Approach
- Property-Directed Reachability (PDR)
- K-Induction


### 2.1 Template-Based (Constraint-Based) Approach

Related work:
- Linear Invariant Generation using Non-linear Constarint Solving, CAV 03
- Constraint-Based Linear-Relations Analysis, SAS'04 
- Non-Linear Loop Invariant Generation using Gröbner Bases, POPL'04 
- Program analysis via constraint solving, PLDI'08 
- Invgen: An efficient invariant generator, CAV'09 
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

#### Abductive Inference

Related work:
- Inductive Invariant Generation via Abductive Inference, OOPSLA 13

TOOD: not implemented yet

#### LLM?
