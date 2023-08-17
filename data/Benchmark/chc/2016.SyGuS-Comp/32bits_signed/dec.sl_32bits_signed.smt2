(set-logic HORN)
(declare-fun inv ((_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32))) 
       (=> ( = x (_ bv100 32) ) (inv x))))
(assert (forall ((x (_ BitVec 32)) (x! (_ BitVec 32))) 
       (=> (and (inv x) ( and ( bvsgt x (_ bv0 32) ) ( = x! ( bvsub x (_ bv1 32) ) ) )) (inv x!))))
(assert (forall ((x (_ BitVec 32))) 
       (=> (inv x) ( not ( and ( bvsle x (_ bv0 32) ) ( not ( = x (_ bv0 32) ) ) ) ))))
(check-sat)