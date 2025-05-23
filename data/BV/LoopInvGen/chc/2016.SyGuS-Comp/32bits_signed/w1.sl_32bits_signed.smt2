(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> ( and ( = x (_ bv0 32) ) ( bvsge n (_ bv0 32) ) ) (inv x n))))
(assert (forall ((x (_ BitVec 32)) (n (_ BitVec 32)) (x! (_ BitVec 32)) (n! (_ BitVec 32))) 
       (=> (and (inv x n) ( and ( = n! n ) ( bvslt x n ) ( = x! ( bvadd x (_ bv1 32) ) ) )) (inv x! n!))))
(assert (forall ((x (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> (inv x n) ( or ( not ( bvsge x n ) ) ( = x n ) ))))
(check-sat)
