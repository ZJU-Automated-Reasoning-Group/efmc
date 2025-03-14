(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> ( and ( = i (_ bv0 32) ) ( bvule (_ bv0 32) k ) ( bvule k (_ bv10 32) ) ) (inv i k))))
(assert (forall ((i (_ BitVec 32)) (k (_ BitVec 32)) (i! (_ BitVec 32)) (k! (_ BitVec 32))) 
       (=> (and (inv i k) ( and ( bvult i ( bvmul (_ bv1000000 32) k ) ) ( = i! ( bvadd i k ) ) ( = k! k ) )) (inv i! k!))))
(assert (forall ((i (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> (inv i k) ( or ( bvult i ( bvmul (_ bv1000000 32) k ) ) ( = i ( bvmul (_ bv1000000 32) k ) ) ))))
(check-sat)
