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



=============
References
=============

