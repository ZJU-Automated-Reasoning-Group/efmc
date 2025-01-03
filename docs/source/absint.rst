Abstraction Interpretation
===========================

Abstraction interpretation is a formal framework for static analysis of programs.
It is based on the idea of abstracting the concrete semantics of a program to
a simpler, more tractable abstract semantics. This abstraction is then used to reason about the program's behavior. The key idea is to over-approximate the set of possible
behaviors of the program, so that the analysis is sound but not necessarily
complete.


===========================
Chaotic Iteration
===========================

The basic idea of abstraction interpretation is to iteratively apply an abstract
transformer to an abstract state until a fixpoint is reached. The abstract
transformer is a function that maps an abstract state to another abstract state.
The fixpoint is reached when the abstract state does not change anymore. 
This process is often called chaotic iteration, and it is guaranteed to converge to a fixpoint

Widening
========

Widening is a technique used in abstract interpretation to ensure the convergence of the iterative analysis process. When the abstract state space is infinite or very large, the analysis might not reach a fixpoint in a reasonable amount of time. Widening accelerates the convergence by forcing the iteration to jump to a broader abstract state, effectively over-approximating the union of the states encountered during the iteration. This guarantees that the analysis will terminate, although it may result in a less precise fixpoint.

Lookahead Widening
----------------------

Guided Static Analysis
-----------------------

Widening with Thresholds
------------------------

Policy Iteration
-----------------------


===========================
Systematic Abstraction
===========================

Making Abstraction Interpretation Complete
==========================================



=============================
Abstract Interpretation Tools
=============================

Astree: developed by the French Space Agency (CNES) for the verification of critical embedded software.

PolySpace: by MathWorks for the verification of embedded software.

CodeSonar: by GrammaTech


TVLA: by Tom Reps and his group at the University of Wisconsin-Madison, as well as Mooly Sagiv and his group at Tel Aviv University.

IKOS: by NASA 

Crab

===========================
References
===========================

.. [CousotCousot77] P. Cousot and R. Cousot. Abstract interpretation: A unified lattice model for static analysis of programs by construction or approximation of fixpoints. In Proceedings of the 4th ACM SIGACT-SIGPLAN symposium on Principles of programming languages, pages 238-252, 1977.
.. [CousotCousot92] P. Cousot and R. Cousot. Abstract interpretation frameworks. Journal of Logic and Computation, 2(4):511-547, 1992.
.. [CousotCousot99] P. Cousot and R. Cousot. Systematic design of program analysis frameworks. In Proceedings of the 6th ACM SIGACT-SIGPLAN symposium on Principles of programming languages, pages 269-282, 1999.
.. [Reps94] T. Reps. Solving demand versions of interprocedural analysis problems. In Proceedings of the 5th International Conference on Compiler Construction, pages 389-403, 1994.
.. [Reps97] T. Reps, S. Horwitz, and M. Sagiv. Precise interprocedural dataflow analysis via graph reachability. In Proceedings of the 22nd ACM SIGPLAN-SIGACT symposium on Principles of programming languages, pages 49-61, 1995.
.. [Reps98] T. Reps, S. Horwitz, M. Sagiv, and G. Rosay. Speeding up slicing. In Proceedings of the 2nd ACM SIGSOFT symposium on Foundations of software engineering, pages 11-20, 1994.