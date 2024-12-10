(set-logic HORN)
(declare-fun inv ((_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64))) 
       (=> ( = x (_ bv0 64) ) (inv x))))
(assert (forall ((x (_ BitVec 64)) (x! (_ BitVec 64))) 
       (=> (and (inv x) ( = x! (_ bv1 64) )) (inv x!))))
(assert (forall ((x (_ BitVec 64))) 
       (=> (inv x) ( not ( = x (_ bv0 64) ) ))))
(check-sat)