PolyHorn Engine
===============

The PolyHorn engine is a specialized verification component within EFMC that handles polynomial constraint systems using advanced mathematical theorems. It provides a powerful framework for solving satisfiability problems involving polynomial inequalities and universally quantified formulas.

Overview
--------

PolyHorn implements three fundamental mathematical theorems for polynomial constraint solving:

- **Farkas' Lemma**: For linear polynomial constraints
- **Handelman's Theorem**: For polynomial constraints with linear left-hand sides  
- **Putinar's Theorem**: For general polynomial constraints using sum-of-squares decomposition

The engine automatically selects the most appropriate theorem based on the structure of the input constraints, or allows manual selection through configuration.

Theoretical Background
----------------------

Farkas' Lemma
~~~~~~~~~~~~~

Farkas' Lemma provides a fundamental result in linear programming theory. For a system of linear inequalities :math:`Ax \geq 0`, the lemma states that either the system has a solution, or there exists a vector :math:`y \geq 0` such that :math:`A^T y = 0` and :math:`y \neq 0`.

In the context of PolyHorn, Farkas' Lemma is used to handle constraint systems of the form:

.. math::
   \forall x. (f_1(x) \geq 0 \land \ldots \land f_n(x) \geq 0) \Rightarrow g(x) \geq 0

where all :math:`f_i` and :math:`g` are linear polynomials.

Handelman's Theorem
~~~~~~~~~~~~~~~~~~~

Handelman's Theorem extends Farkas' Lemma to handle polynomial constraints where the left-hand side consists of linear constraints but the right-hand side can be polynomial. It states that if a polynomial is positive on a basic closed semialgebraic set defined by linear inequalities, then it can be represented as a positive combination of products of the defining linear forms.

Putinar's Theorem
~~~~~~~~~~~~~~~~~

Putinar's Theorem provides the most general framework using sum-of-squares (SOS) decomposition. It handles arbitrary polynomial constraint systems by representing positive polynomials as sums of squares plus combinations of constraint polynomials multiplied by sums of squares.

For a constraint system defined by polynomial inequalities :math:`g_1(x) \geq 0, \ldots, g_m(x) \geq 0`, if a polynomial :math:`f(x)` is positive on the feasible region, then:

.. math::
   f(x) = \sigma_0(x) + \sum_{i=1}^m \sigma_i(x) \cdot g_i(x)

where each :math:`\sigma_i(x)` is a sum of squares.

Usage
-----

Basic API Usage
~~~~~~~~~~~~~~~

The PolyHorn engine can be used through its main API function:

.. code-block:: python

   from efmc.engines.polyhorn.main import execute
   from pysmt.shortcuts import *
   from pysmt.typing import REAL

   # Create symbols
   x = Symbol("x", REAL)
   y = Symbol("y", REAL)
   
   # Create a solver and add constraints
   solver = Solver(name="z3")
   solver.add_assertion(x >= Real(0))
   solver.add_assertion(y >= Real(0))
   solver.add_assertion(ForAll([x, y], 
                              Implies(And(x >= Real(1), y >= Real(1)),
                                     x + y >= Real(2))))
   
   # Configure the engine
   config = {
       "theorem_name": "auto",  # or "farkas", "handelman", "putinar"
       "solver_name": "z3",
       "degree_of_sat": 2,
       "degree_of_nonstrict_unsat": 2
   }
   
   # Execute
   result, model = execute(solver, config)
   print(f"Result: {result}")
   print(f"Model: {model}")

Configuration Options
~~~~~~~~~~~~~~~~~~~~~

The PolyHorn engine supports various configuration parameters:

**Core Settings:**

- ``theorem_name``: Choice of theorem ("farkas", "handelman", "putinar", or "auto")
- ``solver_name``: Backend SMT solver ("z3", "cvc4", etc.)
- ``integer_arithmetic``: Whether to use integer arithmetic (default: False)

**Degree Control:**

- ``degree_of_sat``: Maximum degree for satisfiability constraints
- ``degree_of_nonstrict_unsat``: Maximum degree for non-strict unsatisfiability constraints  
- ``degree_of_strict_unsat``: Maximum degree for strict unsatisfiability constraints
- ``max_d_of_strict``: Degree of variables generated for strict cases in Putinar's theorem

**Heuristics:**

- ``SAT_heuristic``: Enable satisfiability-based heuristics
- ``unsat_core_heuristic``: Enable unsatisfiable core-based optimization

Input Formats
~~~~~~~~~~~~~

PolyHorn accepts input in two main formats:

**SMT2 Format:**

.. code-block:: smt2

   (declare-const x Real)
   (declare-const y Real)
   (assert (forall ((l Real)) 
           (=> (and (= x l) (>= x 1) (<= x 3))
               (and (<= x 10) (= l 2) (> x 0)))))
   (check-sat)
   (get-model)

**PySMT Solver Objects:**

The engine can directly work with PySMT solver objects, automatically converting them to the internal representation.

Implementation Details
----------------------

Core Components
~~~~~~~~~~~~~~~

**Parser (Parser.py)**
  Handles parsing of both SMT2 format and a custom readable format. Supports complex polynomial expressions and constraint systems.

**PositiveModel (PositiveModel.py)**
  The main orchestrator class that manages constraint generation, theorem selection, and solver interaction.

**Theorem Implementations:**
  - ``Farkas.py``: Implements Farkas' Lemma for linear constraints
  - ``Handelman.py``: Implements Handelman's Theorem with monomial generation
  - ``Putinar.py``: Implements Putinar's Theorem with sum-of-squares decomposition

**Polynomial Representation:**
  - ``Polynomial.py``: Core polynomial data structure
  - ``Coefficient.py``: Handles polynomial coefficients with unknown variables
  - ``Constraint.py``: Represents polynomial constraints and inequalities

**Solver Integration (Solver.py)**
  Provides utilities for constraint generation, SMT format conversion, and variable management.

Automatic Theorem Selection
~~~~~~~~~~~~~~~~~~~~~~~~~~~

When ``theorem_name`` is set to "auto", PolyHorn automatically selects the most appropriate theorem:

1. **Farkas' Lemma**: If both left-hand side and right-hand side constraints are linear
2. **Handelman's Theorem**: If left-hand side is linear but right-hand side is polynomial  
3. **Putinar's Theorem**: For general polynomial constraint systems

This selection optimizes both performance and completeness based on the constraint structure.

Advanced Features
-----------------

Sum-of-Squares Optimization
~~~~~~~~~~~~~~~~~~~~~~~~~~~

For Putinar's theorem, PolyHorn generates sum-of-squares templates using semidefinite programming techniques. The implementation creates lower triangular matrices and computes their products to ensure positive semidefiniteness.

Degree Management
~~~~~~~~~~~~~~~~~

The engine provides fine-grained control over polynomial degrees in different contexts:

- Satisfiability constraints can use different degree bounds than unsatisfiability constraints
- Strict and non-strict inequalities are handled with separate degree parameters
- Automatic degree escalation for improved completeness

Core Iteration Heuristic
~~~~~~~~~~~~~~~~~~~~~~~~~

PolyHorn implements an unsatisfiable core-based optimization that iteratively removes unnecessary constraints to simplify the solving process while maintaining correctness.

Examples
--------

Linear Constraint System
~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # System: x >= 0, y >= 0 ⊢ x + y >= 0
   solver = Solver(name="z3")
   solver.add_assertion(ForAll([x, y],
                              Implies(And(x >= Real(0), y >= Real(0)),
                                     x + y >= Real(0))))
   
   config = {"theorem_name": "farkas", "solver_name": "z3"}
   result, model = execute(solver, config)

Polynomial Constraint System
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # System with quadratic constraints
   solver = Solver(name="z3")
   solver.add_assertion(ForAll([x, y],
                              Implies(And(x*x + y*y <= Real(1)),
                                     x*x <= Real(1))))
   
   config = {
       "theorem_name": "putinar", 
       "solver_name": "z3",
       "degree_of_sat": 4
   }
   result, model = execute(solver, config)

Performance Considerations
--------------------------

**Degree Selection**: Higher degrees provide more completeness but significantly increase computational cost. Start with low degrees (0-2) and increase as needed.

**Theorem Choice**: Farkas' Lemma is fastest for linear systems, while Putinar's theorem is most general but computationally expensive.

**Solver Backend**: Z3 generally provides the best performance for the generated constraint systems.

**Memory Usage**: Sum-of-squares decomposition can generate large constraint systems. Monitor memory usage for high-degree problems.

Limitations
-----------

- **Decidability**: While theoretically complete for real arithmetic, practical decidability depends on degree bounds
- **Integer Arithmetic**: Limited support for integer constraints compared to real arithmetic
- **Scalability**: Performance degrades significantly with increasing polynomial degrees and variable counts
- **Numerical Stability**: High-degree polynomials may suffer from numerical precision issues

Integration with EFMC
---------------------

PolyHorn integrates seamlessly with the broader EFMC verification framework:

- **CHC Support**: Handles Constrained Horn Clauses with polynomial constraints
- **Template Integration**: Works with EFMC's template-based verification engines
- **Multi-Engine Workflows**: Can be combined with other EFMC engines for hybrid verification approaches

The engine is particularly effective for verification problems involving:

- Polynomial loop invariants
- Nonlinear arithmetic properties  
- Optimization and control system verification
- Hybrid system analysis

References
----------

1. Farkas, J. (1902). Theorie der einfachen Ungleichungen
2. Handelman, D. (1988). Representing polynomials by positive linear functions on compact convex polyhedra
3. Putinar, M. (1993). Positive polynomials on compact semi-algebraic sets
4. Parrilo, P. A. (2003). Semidefinite programming relaxations for semialgebraic problems
5. Lasserre, J. B. (2001). Global optimization with polynomials and the problem of moments
