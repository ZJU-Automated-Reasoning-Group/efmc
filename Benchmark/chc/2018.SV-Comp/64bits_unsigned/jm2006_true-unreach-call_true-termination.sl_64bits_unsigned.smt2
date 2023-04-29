(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> ( and ( bvuge i (_ bv0 64) ) ( bvuge j (_ bv0 64) ) ( = x i ) ( = y j ) ) (inv i j x y))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64))) 
       (=> (and (inv i j x y) ( and ( not ( = x (_ bv0 64) ) ) ( = i! i ) ( = j! j ) ( = x! ( bvsub x (_ bv1 64) ) ) ( = y! ( bvsub y (_ bv1 64) ) ) )) (inv i! j! x! y!))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> (inv i j x y) ( or ( not ( = x (_ bv0 64) ) ) ( => ( = i j ) ( = y (_ bv0 64) ) ) ))))
(check-sat)
