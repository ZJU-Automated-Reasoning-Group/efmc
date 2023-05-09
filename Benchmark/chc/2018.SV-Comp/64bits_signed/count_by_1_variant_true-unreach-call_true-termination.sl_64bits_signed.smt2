(set-logic HORN)
(declare-fun inv ((_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64))) 
       (=> ( = i (_ bv0 64) ) (inv i))))
(assert (forall ((i (_ BitVec 64)) (i! (_ BitVec 64))) 
       (=> (and (inv i) ( and ( not ( = i (_ bv1000000 64) ) ) ( = i! ( bvadd i (_ bv1 64) ) ) )) (inv i!))))
(assert (forall ((i (_ BitVec 64))) 
       (=> (inv i) ( or ( not ( = i (_ bv1000000 64) ) ) ( bvsle i (_ bv1000000 64) ) ))))
(check-sat)
