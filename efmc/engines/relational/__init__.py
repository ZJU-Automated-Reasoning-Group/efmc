"""Relational verification, verifying hyper-property, verifying k-safety, ...

Equivalence: Forall x, y . x = y => f(x) = g(y)
Monotonicity            x2 <= x1;  f(x);   ret2 <= ret1
Determinism             X1 = X2;   f(X);   ret1 = ret2
Injectivity             X1 != X2;  f(X);   ret1 != ret2

Symmetric relation, anti-symmetric relation, asymmetric relation,
transitive relation, total relation, associativity, homomorphism, idempotence,...?
"""