# Data Directory

This directory contains benchmark files and test cases for the EFMC project.
The benchmark files are primarily in SMT2 and SyGuS(Inv) format.


### Demo/
Contains demonstration Constraint Horn Clauses (CHC) files (in SMT-LIB2 format) showcasing basic examples:
- `fib13_8u.smt2`, `fib10_8u.sm2`, `fib04_32u.smt2` - Fibonacci sequence examples with different bit-vector sizes

### BV/ (Bit-Vector Benchmarks)
Contains bit-vector related benchmark files organized in subdirectories:
- `multi-phase/` - Multi-phase verification benchmarks
  - `sygus/` - SyGuS format benchmarks
  - `chc/` - Constrained Horn Clause benchmarks
- `LoopInvGen/` - Loop invariant generation benchmarks  
- `CAV19/` - Benchmarks from CAV 2019 conference


### INT/ (Integer Benchmarks)
Contains integer arithmetic benchmark files:
- `multi-phase/` - Multi-phase verification benchmarks for integers
- `sygus-inv/` - SyGuS invariant synthesis benchmarks



## More Benchmarks

- https://github.com/sosy-lab/sv-benchmarks/tree/master/clauses

We can find much longer CHC instances (e.g., clauses/ALIA/sdv, where is from Microsfot's device driver verification instances.)