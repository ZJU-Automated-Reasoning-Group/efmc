(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((x (_ BitVec 8)) (n (_ BitVec 8))) 
       (=> ( and ( bvsgt n (_ bv0 8) ) ( = x (_ bv0 8) ) ) (inv x n))))
(assert (forall ((x (_ BitVec 8)) (n (_ BitVec 8)) (x! (_ BitVec 8)) (n! (_ BitVec 8))) 
       (=> (and (inv x n) ( or ( and ( bvsge x n ) ( = x! x ) ( = n! n ) ) ( and ( bvslt x n ) ( = x! ( bvadd x (_ bv1 8) ) ) ( = n! n ) ) )) (inv x! n!))))
(assert (forall ((x (_ BitVec 8)) (n (_ BitVec 8))) 
       (=> (inv x n) ( => ( bvsge x n ) ( = x n ) ))))
(check-sat)
