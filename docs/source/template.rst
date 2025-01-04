Template-based Invariant Generation
=====================================


Invariants are assertions about program variables that hold true throughout the execution of a program. They are used in program verification to describe sets of reachable program states and are an essential tool for reasoning about program correctness. In this section, we demonstrate how to compute invariants that prove certain error locations in a program to be unreachable using constraint-based techniques.

These methods directly encode the sufficiency of invariants (encoding the entire program body) as a constraint and solve the constraint in the following way:

- First, a template assertion that represents the invariant is fixed in a pre-selected language. The template assertion involves program variables X and a set of parameters.

- Next, the constraints on these parameters are defined in a way that corresponds to the definition of the invariant. This means that every solution to the constraint system produces a sound inductive invariant.

- Finally, the values of the parameters are obtained by solving the resulting constraint system.

The key verification conditions are:

- :math:`\forall x. pre(x) \Rightarrow Inv(x)`

- :math:`\forall x. Inv(x) \land G(x) \land T(X, X') \Rightarrow Inv(X')`

- :math:`\forall x . Inv(x) \land G(x) \Rightarrow Post(x)`


=======================
Linear Arithmetic
=======================

In xx, Farkas' Lemma is used to eliminate universal quantifiers and propose a sound and complete constraint-solving framework for generating linear invariants. The result is a set of existentially quantified nonlinear constraints involving template parameters and parameters introduced by Farkas' Lemma. Finally, the problem is simplified to the satisfiability problem of quantifier-free nonlinear arithmetic formulas.

Linear Invariants
------------------

Consider the following simple program::

    int i = 0;
    while (i < 10) {
        i = i + 1
    }
    assert(i == 10);

Nonlinear Invariants
------------------


=======================
Nonlinear Arithmetic
=======================