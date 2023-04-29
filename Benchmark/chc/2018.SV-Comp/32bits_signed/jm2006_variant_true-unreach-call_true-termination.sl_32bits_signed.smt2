(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32))) 
       (=> ( and ( bvsge i (_ bv0 32) ) ( bvsge j (_ bv0 32) ) ( = z (_ bv0 32) ) ( = x i ) ( = y j ) ) (inv i j x y z))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (i! (_ BitVec 32)) (j! (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (z! (_ BitVec 32))) 
       (=> (and (inv i j x y z) ( and ( not ( = x (_ bv0 32) ) ) ( = i! i ) ( = j! j ) ( = x! ( bvsub x (_ bv1 32) ) ) ( = y! ( bvsub y (_ bv2 32) ) ) ( = z! ( bvadd z (_ bv1 32) ) ) )) (inv i! j! x! y! z!))))
(assert (forall ((i (_ BitVec 32)) (j (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32))) 
       (=> (inv i j x y z) ( or ( not ( = x (_ bv0 32) ) ) ( => ( = i j ) ( = y ( bvsub (_ bv0 32) z ) ) ) ))))
(check-sat)
