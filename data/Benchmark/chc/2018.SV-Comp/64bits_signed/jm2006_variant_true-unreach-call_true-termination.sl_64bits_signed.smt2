(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64))) 
       (=> ( and ( bvsge i (_ bv0 64) ) ( bvsge j (_ bv0 64) ) ( = z (_ bv0 64) ) ( = x i ) ( = y j ) ) (inv i j x y z))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (z! (_ BitVec 64))) 
       (=> (and (inv i j x y z) ( and ( not ( = x (_ bv0 64) ) ) ( = i! i ) ( = j! j ) ( = x! ( bvsub x (_ bv1 64) ) ) ( = y! ( bvsub y (_ bv2 64) ) ) ( = z! ( bvadd z (_ bv1 64) ) ) )) (inv i! j! x! y! z!))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64))) 
       (=> (inv i j x y z) ( or ( not ( = x (_ bv0 64) ) ) ( => ( = i j ) ( = y ( bvsub (_ bv0 64) z ) ) ) ))))
(check-sat)
