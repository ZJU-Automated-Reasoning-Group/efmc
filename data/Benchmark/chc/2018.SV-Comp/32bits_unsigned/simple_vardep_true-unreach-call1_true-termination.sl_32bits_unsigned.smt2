(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> ( and ( = i (_ bv0 32) ) ( = j (_ bv0 32) ) ( = k (_ bv0 32) ) ) (inv i j k))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32)) (i! (_ BitVec 32)) (j! (_ BitVec 32)) (k! (_ BitVec 32))) 
       (=> (and (inv i j k) ( and ( bvult k (_ bv268435455 32) ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = j! ( bvadd j (_ bv2 32) ) ) ( = k! ( bvadd k (_ bv3 32) ) ) )) (inv i! j! k!))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> (inv i j k) ( or ( bvult k (_ bv268435455 32) ) ( = k ( bvadd i j ) ) ))))
(check-sat)
