
# TODO List




- Bugs
- Features
- Optimizations


## Bugs 

### The OMT engine of Z3

This bug affects the correctness of `symabs_prover.py`, which relies on 
`symabs/symbolic_abstraction.py` (it uses OMT of Z3)

Some versions of Z3's Optimize() has bugs
Maybe we should be able to choose self-compiled/pre-built python packages for Z3.
Hopefully, the new version are OK.

## New Features

### Features: K-Induction

Need fixing


### Features: Template-based Invariant Inference

We should focus on the template-based invariant inference
- Add the support of zone and octagon domains
- Add Farkas' Lemma based reduction 
- Parallel benchmarking and stats.
- Configurable third-party SMT engines (either via PySMT or via PIPE)

NOTE: to perform the empirical study, we have two choices
-  NRA or LRA: templates + exists-forall solving
-  QF_NRA: templates + Farkas' lemma (for removing universal quantifiers)
(For evaluation, we can add UF to NRA/LRA)

### Features: Template-based Invariant Inference over Bit-Vec

This is important for evaluating EFSMT(BV) and other algorithms.
It is also important to "beat" many existing tools (as they do not support bit-level precision 
memory model.)

04.17: a small example and basic implementation of interval

For more benchmarks, we may use:
https://github.com/chc-comp/vmt-chc-benchmarks/tree/master/bv


### Features: Abduction-based Invariant Inference

- Dillig's abduction algorithm
- Dillig's abduction-based invariant inference algorithm


### Features: K-Induction

### Features: Frontends

### Features: More Expressive Programs/Constraints

- ALIA
- BV
- String
- Algebraic Datatypes
- Container
- FP

### Features: SyGuS

Call SyGuS as a sub-procedure
- CVC5


### Features: Logging

...




## Optimizations

### Optimizations: Irrelevant Variables

The queries from 2018.NeurIPS_Code2Inv may have many variables (e.g., 12). However, most of then are not changed. The final desired invariant may only need 
very few of them.



