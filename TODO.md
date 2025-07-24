# TODO List

Here are a few topics for further exploration:

- Dataset
- Bugs and Issues
- New Features
- Optimizations

## 1. Dataset

First, we need to collect more benchmarks with known oracles (safe or unsafe.), espcially for bit-vector semantics.
If safe, it is better to provide the inductive invariant.
If unsafe, it is better to provide the counterexample.

Second, we need a regression system for tracking the correctness and performance of new features.

## 2. New Features

### Frontend

Currently, we have limited support for frontends and types of transition systems. The capabilities of different engines vary significantly (ALIA, BV, String, Algebraic Datatypes, Container, etc.).

We need to improve the frontend to enhance applicability:

- C to SyGuS
- C to CHC (Eldarica, Linear-Arbitrary support)
- C to TransitionSystem
- Btor?
- Boogie
- VMT (Verification Modolo THeories)
- MCMT(?)
- Lustre
- Simulink
- Floating points
- ...?

Related work:

- The CoSA model checker supports many kinds of inputs (it relies on pySMT and is not maintained anymore) [CoSA](https://github.com/cristian-mattarei/CoSA)

### Template-based (Constraint-based) Invariant Inference

This is the original goal of the project.

#### For Integer and Real Semantics

- Add Farkas' Lemma-based reduction (`efmc/engines/ef/farkas`, not finished yet)

We have two choices:

- NRA or LRA: templates + exists-forall solving
- QF_NRA: templates + Farkas' Lemma (for removing universal quantifiers)
  (For evaluation, we can add UF to NRA/LRA)

#### For Bit-Vector Semantics

- Accelerating EF(BV) solving: `efsmt_par.py` (multi-process, uses SMT-LIB2 string communication, relatively slow; may have bugs)
- More invariant templates: E.g., bit-wise templates (parity, bit-mask, ...?)

- More benchmarks, e.g.,: [vmt-chc-benchmarks](https://github.com/chc-comp/vmt-chc-benchmarks/tree/master/bv)

#### Beyond Invariants

Currently, the encoding is not very flexible. For example, we may use the template-based approach for generating ranking functions (to prove termination).


### Abduction-based Invariant Inference

- Dillig's abduction algorithm
- Other abduction algorithms
- Dillig's abduction-based invariant inference algorithm
- Other abduction-based invariant inference algorithms

## 3. Optimizations

### Various Forms of Simplifications (Slicing, etc.)

For example, the queries from 2018.NeurIPS_Code2Inv may have many variables (e.g., 12). However, most of them are not changed, and the final desired invariant may only need a few of them. Currently, the encoding used by the `efsmt_solver` is somewhat inefficient.
