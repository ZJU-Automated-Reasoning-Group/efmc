(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32))) 
       (=> ( = x (_ bv0 32) ) (inv x y z))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (z! (_ BitVec 32))) 
       (=> (and (inv x y z) ( or ( and ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! z! ) ( bvule z! y ) ( bvult x (_ bv500 32) ) ) ( and ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! y ) ( bvugt z! y ) ( bvult x (_ bv500 32) ) ) )) (inv x! y! z!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32))) 
       (=> (inv x y z) ( not ( and ( bvuge x (_ bv500 32) ) ( bvult z y ) ) ))))
(check-sat)