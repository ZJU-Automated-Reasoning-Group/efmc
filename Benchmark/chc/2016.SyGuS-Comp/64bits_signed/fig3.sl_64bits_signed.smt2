(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (lock (_ BitVec 64))) 
       (=> ( or ( and ( = x y ) ( = lock (_ bv1 64) ) ) ( and ( = ( bvadd x (_ bv1 64) ) y ) ( = lock (_ bv0 64) ) ) ) (inv x y lock))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (lock (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (lock! (_ BitVec 64))) 
       (=> (and (inv x y lock) ( or ( and ( not ( = x y ) ) ( = lock! (_ bv1 64) ) ( = x! y ) ) ( and ( not ( = x y ) ) ( = lock! (_ bv0 64) ) ( = x! y ) ( = y! ( bvadd y (_ bv1 64) ) ) ) )) (inv x! y! lock!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (lock (_ BitVec 64))) 
       (=> (inv x y lock) ( not ( and ( = x y ) ( not ( = lock (_ bv1 64) ) ) ) ))))
(check-sat)
