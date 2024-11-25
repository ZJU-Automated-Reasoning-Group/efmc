(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (k (_ BitVec 32)) (j (_ BitVec 32))) 
       (=> ( and ( = i (_ bv0 32) ) ( = k (_ bv0 32) ) ) (inv i k j))))
(assert (forall ((i (_ BitVec 32)) (k (_ BitVec 32)) (j (_ BitVec 32)) (i! (_ BitVec 32)) (k! (_ BitVec 32)) (j! (_ BitVec 32))) 
       (=> (and (inv i k j) ( and ( bvslt i (_ bv1000000 32) ) ( bvsle (_ bv1 32) j! ) ( bvslt j! (_ bv1000000 32) ) ( = i! ( bvadd i j! ) ) ( = k! ( bvadd k (_ bv1 32) ) ) )) (inv i! k! j!))))
(assert (forall ((i (_ BitVec 32)) (k (_ BitVec 32)) (j (_ BitVec 32))) 
       (=> (inv i k j) ( or ( bvslt i (_ bv1000000 32) ) ( bvsle k (_ bv1000000 32) ) ))))
(check-sat)
