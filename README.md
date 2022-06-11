
# A Toolkit for Inductive Invariant Generation


## 1. Current Features

### Template-based (Constraint-based) Approach

Related work:
- Linear Invariant Generation using Non-linear Constarint Solving, CAV 03
- Program Analysis via Constraint Solving, PLDI 08

Currently, we do not apply Farkas' lemma now, but use exists-forall SMT solving.

### Abuductive Inference

Related work:
- Inductive Invariant Generation via Abductive Inference, OOPSLA 13

### Predicate Abstraction 
Currently, we have a very basic version (not used now).

### Symbolic Abstraction
Currently, we have a very basic version (only interval domain, no join and widening)


### Quantifier Elimination 
This one strictly follows the definition of strongest post-condition,
which means we use quantifier elimination to compute the "image operation".
But for loop, we use fixed-point iteration.

## 2. Future Extensions


### Algorithms (usually) that Require Interpolants

- IMPACT (lazy abstraction using interpolation)
- IC3/PDR (some implementations do not need)
- Trace abstraction

### Conventional Abstract Interpretation