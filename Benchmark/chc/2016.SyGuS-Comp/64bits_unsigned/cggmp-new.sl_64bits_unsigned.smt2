(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64))) 
       (=> ( and ( = i (_ bv1 64) ) ( = j (_ bv20 64) ) ) (inv i j))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64))) 
       (=> (and (inv i j) ( and ( bvuge j i ) ( = i! ( bvadd i (_ bv2 64) ) ) ( = j! ( bvsub j (_ bv1 64) ) ) )) (inv i! j!))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64))) 
       (=> (inv i j) ( not ( and ( bvult j i ) ( not ( = j (_ bv13 64) ) ) ) ))))
(check-sat)
