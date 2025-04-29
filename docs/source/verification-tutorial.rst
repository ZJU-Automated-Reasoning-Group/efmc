Playing wiht Program Verification with EFMC
==========================


This tutorial provides a step-by-step guide to program verification using EFMC.

1. Setup and Installation
------------------------

First, ensure you have EFMC installed::

    # Create and activate a virtual environment (recommended)
    python -m venv venv
    source venv/bin/activate  # On Unix/macOS
    # or
    .\venv\Scripts\activate  # On Windows

    # Install EFMC
    pip install -e .

2. Understanding Input Formats
----------------------------

EFMC supports two main input formats:

1. CHC (Constrained Horn Clauses)
2. SyGuS (Syntax-Guided Synthesis)

Example CHC File
~~~~~~~~~~~~~~~

Here's a simple example (``fib04_32u.smt2``)::

    (set-logic HORN)
    (declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
    (assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
           (=> ( = x ( bvadd (_ bv1 32) ( bvnot (_ bv50 32) ) ) ) (inv x y))))
    (assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
           (=> (and (inv x y) ( or ( and ( bvult x (_ bv0 32) ) ( = x! ( bvadd x y ) ) ( = y! ( bvadd y (_ bv1 32) ) ) ) ( and ( bvuge x (_ bv0 32) ) ( = x! x ) ( = y! y ) ) )) (inv x! y!))))
    (assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
           (=> (inv x y) ( => ( not ( bvult x (_ bv0 32) ) ) ( bvuge y (_ bv0 32) ) ))))
    (check-sat)

This example represents:

- Program with two variables: ``x`` and ``y``
- Initial condition: ``x = -50``
- Property to verify: When ``x ≥ 0``, then ``y ≥ 0``

3. Basic Verification
-------------------

Running Verification
~~~~~~~~~~~~~~~~~~

You can verify programs using different engines:

1. Template-based Verification::

    efmc --engine ef --template bv_interval --lang chc --file your_file.smt2

2. PDR (Property-Directed Reachability)::

    efmc --engine pdr --lang chc --file your_file.smt2

3. K-Induction::

    efmc --engine kind --lang chc --file your_file.smt2

Understanding Results
~~~~~~~~~~~~~~~~~~~

The verifier outputs one of these results:

- ``safe``: Property is verified (program is safe)
- ``unsafe``: A bug is found
- ``unknown``: Verifier cannot determine the result

4. Advanced Verification Techniques
--------------------------------

K-Induction
~~~~~~~~~~

K-induction extends basic inductive verification by considering ``k`` consecutive states:

.. code-block:: bash

    efmc --engine kind --k 3 --lang chc --file your_file.smt2

Template-Based Verification
~~~~~~~~~~~~~~~~~~~~~~~~~

Supports different templates:

- ``bv_interval``: Bit-vector intervals
- ``octagon``: Octagonal constraints
- ``polyhedra``: Polyhedral constraints

Example::

    efmc --engine ef --template polyhedra --lang chc --file your_file.smt2

Property-Directed Reachability (PDR)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Uses Z3's Spacer engine for incremental invariant building::

    efmc --engine pdr --lang chc --file your_file.smt2

5. Best Practices
---------------


Input Format Guidelines
~~~~~~~~~~~~~~~~~~~~

1. Use clear variable naming
2. Specify precise pre and post-conditions


6. Example Workflow
-----------------

Try different engines:

    # Try PDR
    efmc --engine pdr --lang chc --file your_file.smt2

    # Try k-induction
    efmc --engine kind --k 2 --lang chc --file your_file.smt2

    # Try template-based approach
    efmc --engine ef --template bv_interval --lang chc --file your_file.smt2


7. References
-----------

1. Clarke, E. M., Grumberg, O., & Peled, D. A. (1999). Model checking. MIT press.
2. Bradley, A. R., & Manna, Z. (2007). The Calculus of Computation: Decision Procedures with Applications to Verification.
3. Sheeran, M., Singh, S., & Stålmarck, G. (2000). Checking safety properties using induction and a SAT-solver. 