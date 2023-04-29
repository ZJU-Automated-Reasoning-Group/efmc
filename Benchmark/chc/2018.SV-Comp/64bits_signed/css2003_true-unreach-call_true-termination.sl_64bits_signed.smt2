(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64))) 
       (=> ( and ( = i (_ bv1 64) ) ( = j (_ bv1 64) ) ( bvsle (_ bv0 64) k ) ( bvsle k (_ bv1 64) ) ) (inv i j k))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64)) (k! (_ BitVec 64))) 
       (=> (and (inv i j k) ( and ( bvslt i (_ bv1000000 64) ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = j! ( bvadd j k ) ) ( = k! ( bvsub k (_ bv1 64) ) ) )) (inv i! j! k!))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64))) 
       (=> (inv i j k) ( or ( not ( bvslt i (_ bv1000000 64) ) ) ( and ( bvsle (_ bv1 64) ( bvadd i k ) ) ( bvsle ( bvadd i k ) (_ bv2 64) ) ( bvsge i (_ bv1 64) ) ) ))))
(check-sat)
