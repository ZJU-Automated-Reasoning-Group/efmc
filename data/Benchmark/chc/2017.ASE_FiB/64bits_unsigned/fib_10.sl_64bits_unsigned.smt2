(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (w (_ BitVec 64)) (z (_ BitVec 64))) 
       (=> ( and ( = w (_ bv1 64) ) ( = z (_ bv0 64) ) ( = x (_ bv0 64) ) ( = y (_ bv0 64) ) ) (inv x y w z))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (w (_ BitVec 64)) (z (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (w! (_ BitVec 64)) (z! (_ BitVec 64))) 
       (=> (and (inv x y w z) ( or ( and ( = w (_ bv1 64) ) ( = z (_ bv0 64) ) ( = x! ( bvadd x (_ bv1 64) ) ) ( = w! (_ bv0 64) ) ( = y! ( bvadd y (_ bv1 64) ) ) ( = z! (_ bv1 64) ) ) ( and ( not ( = w (_ bv1 64) ) ) ( = z (_ bv0 64) ) ( = x! x ) ( = w! w ) ( = y! ( bvadd y (_ bv1 64) ) ) ( = z! (_ bv1 64) ) ) ( and ( = w (_ bv1 64) ) ( not ( = z (_ bv0 64) ) ) ( = x! ( bvadd x (_ bv1 64) ) ) ( = w! (_ bv0 64) ) ( = y! y ) ( = z! z ) ) ( and ( not ( = w (_ bv1 64) ) ) ( not ( = z (_ bv0 64) ) ) ( = x! x ) ( = w! w ) ( = y! y ) ( = z! z ) ) )) (inv x! y! w! z!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (w (_ BitVec 64)) (z (_ BitVec 64))) 
       (=> (inv x y w z) ( = x y ))))
(check-sat)
