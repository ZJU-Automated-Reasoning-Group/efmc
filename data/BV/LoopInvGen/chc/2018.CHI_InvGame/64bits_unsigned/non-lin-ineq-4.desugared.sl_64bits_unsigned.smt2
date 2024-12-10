(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64))) 
       (=> ( and ( = i (_ bv0 64) ) ( = j (_ bv1 64) ) ( = k (_ bv0 64) ) ) (inv i j k))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64)) (k! (_ BitVec 64))) 
       (=> (and (inv i j k) ( and ( bvult i (_ bv1000 64) ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = j! ( bvadd j (_ bv1 64) ) ) ( = k! ( bvadd k ( bvmul i! j! ) ) ) )) (inv i! j! k!))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64))) 
       (=> (inv i j k) ( or ( bvult i (_ bv1000 64) ) ( bvule ( bvmul (_ bv1000 64) j ) k ) ))))
(check-sat)