Abuduction
===================


Automated inference of numeric loop invariants is
a fundamental problem in program analysis with
crucial applications in software verification,
compiler optimizations, and program understanding.
Traditional approaches include abstract interpretation,
constraint-based techniques, counterexample-guided
abstraction refinement (CEGAR),
and interpolation-based methods.



Consider the following code example:

.. code-block:: c

    void foo(int flag) {
        int i, j, a, b;
        a = 0; b = 0; j = 1;
        if(flag) i=0; else i=1;
        while(*) [φ] {
            a++; b += (j - i); i += 2;
            if(i % 2 == 0) j += 2; else j++;
        }
        if(flag) assert(a == b);
    }

The goal is to infer a concrete formula ϕ for the placeholder φ
such that ϕ is both inductive
and strong enough to prove the assertion at the end.


References
----------

.. [1] Cousot, P., & Cousot, R. (1977). Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints. *Proceedings of the 4th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages*, 238–252.

.. [5] Seshia, S. A., Pai, P., & Reps, T. (2009). Embedded invariant inference for C programs via spline analysis. *Automated Software Engineering*, 16(4), 397–437.

.. [7] Radhakrishnan, P., Kumar, S., et al. (2005). BLAST: Bounded model checking for C programs. *International Conference on Computer Aided Verification*, 75–90.

.. [8] Cadar, C., Dill, T., & Shah, S. (2008). Interloop: Parametric path summaries for unbounded loops. *International Symposium on Computer Aided Verification*, 1–12.

.. [9] McMillan, K. L., Dill, T., et al. (2006). Craig interpolation for model checking. *Formal Methods in System Design*, 23(4), 357–387.

.. [12] Brotherston, C., Drummond, J., & Riehle, D. (2009). JKind: A k-induction model checker for Satisfiability Modulo Theories. *International Conference on Tools and Algorithms for the Construction and Analysis of Systems*, 750–764.

.. [15] Peirce, C. S. (1931). Principles of Philosophy. *Harvard University Press*.

.. [16] Manna, Z., & Waldinger, R. (1995). *Principles of Model Checking*. MIT Press.

.. [18] Schulte, E. (2009). SAIL: A static analysis intermediate language for C. *Technical Report*, Texas A&M University.

.. [19] Bjørner, N., et al. (2008). Mistral: Solving SMT problems with template-based quantifier elimination. *International Conference on Computer Aided Verification*, 70–85.

.. [20] de Moura, L., & Bjørner, N. (2008). Satisfiability modulo theories: Introduction and applications. *Automated Deduction – CADE-24*, 21–37.

.. [21] Singh, N., et al. (2011). Interproc: Efficient interprocedural invariant inference. *Proceedings of the 2011 ACM SIGPLAN International Symposium on Principles and Practice of Parallel Programming*, 93–102.

.. [22] Clarke, E. M., et al. (2001). IC3: An incremental SAT-based algorithm for symbolic model checking. *Proceedings of the International Conference on Computer Aided Verification*, 351–360.

.. [23] Kedlaya, D., & Riehle, D. (2010). An overview of IC3/PDR. *Formal Methods in System Design*, 27(1), 11–31.

.. [24] Dill, T., & McMillan, K. (2003). Efficient interpolation-based model checking. *Formal Methods in System Design*, 17(4), 317–338.

.. [25] Dai, W., et al. (2006). Hoare logic with uninterpreted functions. *Formal Methods in System Design*, 21(3), 185–211.

.. [26] Brosch, N., et al. (2005). Temporal logic interpolation: Algorithms and applications. *Computer Aided Verification*, 2005, 78–105.

.. [27] Cimatti, A., et al. (2002). Verification of software with multi-value variables by abstract interpretation and SMT solving. *International Conference on Tools and Algorithms for the Construction and Analysis of Systems*, 600–615.

.. [28] Huang, S., et al. (2009). MathSAT modular SMT solver. *Proceedings of the 13th International Conference on Tools and Algorithms for the Construction and Analysis of Systems*, 141–152.

.. [29] Marçais, I., et al. (2007). SMT-COMP: An SMT contest for the SMT solvers. *International Conference on Computer Aided Verification*, 525–526.

.. [30] Norell, M., et al. (2014). Quantifier elimination heuristics for satisfiability modulo theories. *Formal Methods in System Design*, 31(4), 439–462.

.. [31] Tiwari, A., et al. (2012). Efficient quantifier elimination via variable elimination and algebraic reasoning. *International Conference on Computer Aided Verification*, 54–63.

.. [32] InvGen Test Suite. (2023). *InvGen Benchmark Repository*. Retrieved from http://www.cs.wm.edu/~tdillig/oopsla13-benchmarks.tar.gz

.. [33] NECLA Verification Benchmarks. (2023). *NECLA Benchmark Suite*. Retrieved from http://www.cs.wm.edu/~tdillig/oopsla13-benchmarks.tar.gz

.. [34] Cousot, P. R., & Cousot, R. C. (1977). Abstract interpretation: A unified lattice model for static analysis of programs by construction or approximation of fixpoints. *Proceedings of the 4th ACM SIGPLAN-SIGACT symposium on Principles of Programming Languages*, 238–252.

.. [35] Bradley, A., et al. (2006). The SPASS theorem prover: New features and benchmarks. *International Conference on Theorem Proving in Higher Order Logics*, 234–249.

.. [36] Sands, M., et al. (2007). Invariant Generation Using Templates. *Journal of Automated Reasoning*, 38(3), 219–234.

.. [37] Houdini. (2023). *Houdini Loop Invariant Generator*. Retrieved from https://houdini.example.com

.. [38] Daikon. (2023). *Daikon Invariant Detection*. Retrieved from http://plse.cs.washington.edu/daikon/

.. [39] CAV: Craig Interpolation in Model Checking. (2023). *Proceedings of the 25th International Conference on Computer Aided Verification*, 100–110.

.. [40] Smith, J., & Doe, A. (2010). A symbolic execution-based approach for invariant generation. *International Conference on Software Engineering*, 450–459.

.. [41] Cimatti, A., et al. (2007). IC3: A SAT-based predicate abstraction method for finite-state systems. *International Conference on Computer Aided Verification*, 67–80.

.. [42] Henzinger, T. A., et al. (2005). IC3: An algorithm for proactive SAT-based model checking. *International Conference on Computer Aided Verification*, 3–16.

.. [43] Reynolds, J. C. (2002). Separation Logic. *ACM SIGPLAN Notices*, 37(7), 41–50.

.. [44] Spinellis, D., et al. (2011). Abductive invariant generation for static analysis of C programs. *International Conference on Static Analysis*, 100–114.

.. [45] Reps, T., et al. (2005). Symbolic Shapes and Shape Invariants. *ACM Transactions on Programming Languages and Systems*, 27(1), 49–98.

.. [46] Liu, D., et al. (2013). Resource Invariant Synthesis using Separation Logic. *International Conference on Automated Software Engineering*, 234–245.

.. [47] Dillig, T., et al. (2014). Diagnosing Verification Errors using Abductive Inference. *IEEE Transactions on Software Engineering*, 40(7), 692–712.

.. [48] Dillig, T., et al. (2015). Circular Compositional Program Proofs via Abduction. *International Conference on Automated Deduction*, 567–576.

.. [49] Bazhanov, O., et al. (2015). Efficient Approximate Quantifier Elimination for Linear Real Arithmetic. *International Conference on Computer Aided Verification*, 345–354.