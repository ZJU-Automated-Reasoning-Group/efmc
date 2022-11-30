
# A Verification Toolkit


## 1. Current Features

### Template-based (Constraint-based) Approach

Related work:
- Linear Invariant Generation using Non-linear Constarint Solving, CAV 03
- Program Analysis via Constraint Solving, PLDI 08
Currently, we do not apply Farkas' lemma, but use exists-forall SMT solving.

To run the engine, you may try two ways:
- Run `prover.py`, which will use `efmc/ef_prover.py`.
- Run the test script in `efmc/test/test_bvinerval.py`



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

## 2. Future Extensions


### Algorithms that (usually) Require Interpolants

- IMPACT (lazy abstraction using interpolation)
- IC3/PDR (some implementations do not need interpolant)
- Trace abstraction

### Conventional Abstract Interpretation