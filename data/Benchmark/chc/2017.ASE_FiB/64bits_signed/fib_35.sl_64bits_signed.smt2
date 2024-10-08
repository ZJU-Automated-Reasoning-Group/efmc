(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> ( and ( bvsgt n (_ bv0 64) ) ( = x (_ bv0 64) ) ) (inv x n))))
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64)) (x! (_ BitVec 64)) (n! (_ BitVec 64))) 
       (=> (and (inv x n) ( or ( and ( bvsge x n ) ( = x! x ) ( = n! n ) ) ( and ( bvslt x n ) ( = x! ( bvadd x (_ bv1 64) ) ) ( = n! n ) ) )) (inv x! n!))))
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> (inv x n) ( => ( bvsge x n ) ( = x n ) ))))
(check-sat)
