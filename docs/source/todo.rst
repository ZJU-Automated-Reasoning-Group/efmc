TODO List
===========================

Here are a few topics for further exploration.

- Bugs and Issues
- New Features
- Optimizations

===============
1.Bugs and Issues
===============

The OMT solving engine of Z3
------------------------------

Some versions of Z3's Optimize() has bugs, which affect the correctness of ``symabs_prover.py``, which relies on
``symabs/symbolic_abstraction.py`` (it uses OMT of Z3)

Maybe we should be able to choose self-compiled/pre-built python packages for Z3.
Hopefully, the new version are OK.

==================
2. New Features
==================

2.0 Frontend
------------------------------

We need to frontend to improve the applicability

- C to SyGuS
- C to CHC (Eldarica, Linera-Arbitrary支持)
- C to TransitionSystem
- Btor?
- MCMT(?)
- Lustre

2.1 Template-based (Constraint-based) Invariant Inference
------------------------------------------------------------

This is the original goal of the project.

For Integer and Real Semantics
------------------------------

- Add Farkas' Lemma based reduction

NOTE: to perform the empirical study, we have two choices:

- NRA or LRA: templates + exists-forall solving
- QF_NRA: templates + Farkas' lemma (for removing universal quantifiers)
  (For evaluation, we can add UF to NRA/LRA)

For Bit-Vector Semantics
------------------------------

This is important for evaluating EFSMT(BV) and other algorithms.
It is also important to "beat" many existing tools (as they do not support bit-level precision
memory model.)

For more benchmarks, we may use:
`<https://github.com/chc-comp/vmt-chc-benchmarks/tree/master/bv>`_

Beyond Invariant
------------------------------

Currently, the encoding is not very flexible.
For example, we may use the template-based approach for generating ranking
functions (to prove termination).

2.2 Different Variants of BMC and K-Induction
------------------------------------------------------------

Need fixing

2.3 Abduction-based Invariant Inference
+++++++++++++++++++++++++++++++++++++

- Dillig's abduction algorithm
- Other abduction algorithms
- Dillig's abduction-based invariant inference algorithm
- Other abduction-based invariant inference algorithms

2.4 Features: Frontends and Transition System
------------------------------------------------------------

Currently, we have limited support for the frontends and types of transition systems.
In particular, the capability of different engines may vary a lot (ALIA, BV,
String, Algebraic Datatypes, Container..)

Related work:

- The CoSA model checker supports many kinds of inputs (it relies on pySMT,
  and is not maintained anymore?) `<https://github.com/cristian-mattarei/CoSA>`_

Perhaps we can integrate CoSA...

Features: More Expressive Programs/Constraints
------------------------------------------------

test

============
3. Optimizations
============

Various Forms of Simplifications (Slicing, etc.)
------------------------------------------------------------

For example, the queries from 2018.NeurIPS_Code2Inv may have many variables (e.g., 12).
However, most of them are not changed, and the final desired invariant may only need very few of them.
Currently, the encoding used by the efsmt_solver is a bit stupid.

