(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> ( and ( = i (_ bv1 32) ) ( = j (_ bv1 32) ) ( bvsle (_ bv0 32) k ) ( bvsle k (_ bv1 32) ) ) (inv i j k))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32)) (i! (_ BitVec 32)) (j! (_ BitVec 32)) (k! (_ BitVec 32))) 
       (=> (and (inv i j k) ( and ( bvslt i (_ bv1000000 32) ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = j! ( bvadd j k ) ) ( = k! ( bvsub k (_ bv1 32) ) ) )) (inv i! j! k!))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> (inv i j k) ( or ( not ( bvslt i (_ bv1000000 32) ) ) ( and ( bvsle (_ bv1 32) ( bvadd i k ) ) ( bvsle ( bvadd i k ) (_ bv2 32) ) ( bvsge i (_ bv1 32) ) ) ))))
(check-sat)
