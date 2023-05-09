(set-logic HORN)
(declare-fun inv ((_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64))) 
       (=> ( = x (_ bv10000 64) ) (inv x))))
(assert (forall ((x (_ BitVec 64)) (x! (_ BitVec 64))) 
       (=> (and (inv x) ( and ( bvsgt x (_ bv0 64) ) ( = x! ( bvsub x (_ bv1 64) ) ) )) (inv x!))))
(assert (forall ((x (_ BitVec 64))) 
       (=> (inv x) ( not ( and ( bvsle x (_ bv0 64) ) ( not ( = x (_ bv0 64) ) ) ) ))))
(check-sat)
