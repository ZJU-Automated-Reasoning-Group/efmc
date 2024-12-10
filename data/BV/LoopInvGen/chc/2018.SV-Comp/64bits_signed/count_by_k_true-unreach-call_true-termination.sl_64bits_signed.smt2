(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (k (_ BitVec 64))) 
       (=> ( and ( = i (_ bv0 64) ) ( bvsle (_ bv0 64) k ) ( bvsle k (_ bv10 64) ) ) (inv i k))))
(assert (forall ((i (_ BitVec 64)) (k (_ BitVec 64)) (i! (_ BitVec 64)) (k! (_ BitVec 64))) 
       (=> (and (inv i k) ( and ( bvslt i ( bvmul (_ bv1000000 64) k ) ) ( = i! ( bvadd i k ) ) ( = k! k ) )) (inv i! k!))))
(assert (forall ((i (_ BitVec 64)) (k (_ BitVec 64))) 
       (=> (inv i k) ( or ( bvslt i ( bvmul (_ bv1000000 64) k ) ) ( = i ( bvmul (_ bv1000000 64) k ) ) ))))
(check-sat)