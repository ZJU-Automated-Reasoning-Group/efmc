(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64))) 
       (=> ( and ( = i (_ bv0 64) ) ( = j (_ bv0 64) ) ( = k (_ bv0 64) ) ) (inv i j k))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64)) (k! (_ BitVec 64))) 
       (=> (and (inv i j k) ( and ( bvult k (_ bv268435455 64) ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = j! ( bvadd j (_ bv2 64) ) ) ( = k! ( bvadd k (_ bv3 64) ) ) )) (inv i! j! k!))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64))) 
       (=> (inv i j k) ( or ( bvult k (_ bv268435455 64) ) ( and ( = k ( bvmul (_ bv3 64) i ) ) ( = j ( bvmul (_ bv2 64) i ) ) ) ))))
(check-sat)
