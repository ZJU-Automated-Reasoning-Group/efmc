(set-logic HORN)
(declare-fun inv ((_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64))) 
       (=> ( bvsge x (_ bv0 64) ) (inv x))))
(assert (forall ((x (_ BitVec 64)) (x! (_ BitVec 64))) 
       (=> (and (inv x) ( and ( bvslt x (_ bv268435455 64) ) ( = x! ( bvadd x (_ bv1 64) ) ) )) (inv x!))))
(assert (forall ((x (_ BitVec 64))) 
       (=> (inv x) ( or ( bvslt x (_ bv268435455 64) ) ( bvsgt x (_ bv268435455 64) ) ))))
(check-sat)
