(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32))) 
       (=> ( and ( = i (_ bv1 32) ) ( = j (_ bv10 32) ) ) (inv i j))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (i! (_ BitVec 32)) (j! (_ BitVec 32))) 
       (=> (and (inv i j) ( and ( bvuge j i ) ( = i! ( bvadd i (_ bv2 32) ) ) ( = j! ( bvadd j ( bvsub (_ bv0 32) (_ bv1 32) ) ) ) )) (inv i! j!))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32))) 
       (=> (inv i j) ( or ( bvuge j i ) ( = j (_ bv6 32) ) ))))
(check-sat)
