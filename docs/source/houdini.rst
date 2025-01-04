Houdini
===================

The Houdini algorithm is a simple and efficient technique for inferring loop invariants. 
It takes as input a set of predicates and outputs the maximal subset of these predicates that are inductive.

The algorithm works as follows:
TBD

The algorithm is interesting for several reasons:
- It is an example of a "guess-and-check" style invariant inference
- It can also be regarded as "template-based" invariant inference
- It is can be used as a building block in more complex invariant inference algorithms.

============
Houdini in EFMC
=============

The Houdini algorithm is implemented in the EFMC tool as a standalone invariant inference module.

=============
References
=============

.. [1] K. R. M. Leino and F. Logozzo, "Houdini, an Annotation Assistant for ESC/Java," in FME, 2001.

