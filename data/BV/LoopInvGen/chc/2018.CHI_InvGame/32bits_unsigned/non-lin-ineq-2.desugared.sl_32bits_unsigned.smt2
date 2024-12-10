(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> ( and ( = i (_ bv0 32) ) ( bvugt j (_ bv0 32) ) ( bvugt k (_ bv0 32) ) ) (inv i j k))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32)) (i! (_ BitVec 32)) (j! (_ BitVec 32)) (k! (_ BitVec 32))) 
       (=> (and (inv i j k) ( and ( bvult i ( bvmul j k ) ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = j! j ) ( = k! k ) )) (inv i! j! k!))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> (inv i j k) ( or ( bvult i ( bvmul j k ) ) ( = i ( bvmul j k ) ) ))))
(check-sat)