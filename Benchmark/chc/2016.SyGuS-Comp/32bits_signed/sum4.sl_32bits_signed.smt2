(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (sn (_ BitVec 32))) 
       (=> ( and ( = sn (_ bv0 32) ) ( = i (_ bv1 32) ) ) (inv i sn))))
(assert (forall ((i (_ BitVec 32)) (sn (_ BitVec 32)) (i! (_ BitVec 32)) (sn! (_ BitVec 32))) 
       (=> (and (inv i sn) ( and ( = i! ( bvadd i (_ bv1 32) ) ) ( bvsle i (_ bv8 32) ) ( = sn! ( bvadd sn (_ bv1 32) ) ) )) (inv i! sn!))))
(assert (forall ((i (_ BitVec 32)) (sn (_ BitVec 32))) 
       (=> (inv i sn) ( or ( bvsle i (_ bv8 32) ) ( = sn (_ bv8 32) ) ( = sn (_ bv0 32) ) ))))
(check-sat)
