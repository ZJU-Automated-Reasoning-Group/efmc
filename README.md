
# A Verification Toolkit


## 1. The Main Engines

- Template-based (Constraint-based) Approach
- Property-Directed Reachability (PDR)
- K-Induction

### Template-based (Constraint-based) Approach

Related work:
- Linear Invariant Generation using Non-linear Constarint Solving, CAV 03
- Program Analysis via Constraint Solving, PLDI 08
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

### Property-Directed Reachability (PDR) Approach
Currently, we use the one inside Z3 (named `Spacer`)

### Simple K-Induction

## 2. Other Engines

Most of them are not finished yet...

### Abductive Inference

Related work:
- Inductive Invariant Generation via Abductive Inference, OOPSLA 13

TOOD: not implemented yet

### Predicate Abstraction 
Currently, we have a very basic version (not used now).
Perhaps it could be useful for Boolean programs.

### Symbolic Abstraction
Currently, we have a very basic version (only interval domain, no join and widening)


### Quantifier Elimination 
This one strictly follows the definition of strongest post-condition,
which means we use quantifier elimination to compute the "image operation".
But for loop, we use fixed-point iteration.


### Algorithms that (usually) Require Interpolants

- IMPACT (lazy abstraction using interpolation)
- IC3/PDR (some implementations do not need interpolant)
- Trace abstraction

### Conventional Abstract Interpretation