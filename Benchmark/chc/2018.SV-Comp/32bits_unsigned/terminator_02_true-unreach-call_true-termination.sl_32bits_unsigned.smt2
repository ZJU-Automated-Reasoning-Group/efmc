(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (z (_ BitVec 32))) 
       (=> ( and ( bvugt x ( bvsub (_ bv0 32) (_ bv100 32) ) ) ( bvult x (_ bv200 32) ) ( bvugt z (_ bv100 32) ) ( bvult z (_ bv200 32) ) ) (inv x z))))
(assert (forall ((x (_ BitVec 32)) (z (_ BitVec 32)) (x! (_ BitVec 32)) (z! (_ BitVec 32))) 
       (=> (and (inv x z) ( let ( ( a!1 ( or ( and ( = x! ( bvadd x (_ bv1 32) ) ) ( = z! z ) ) ( and ( = x! ( bvsub x (_ bv1 32) ) ) ( = z! ( bvsub z (_ bv1 32) ) ) ) ) ) ) ( and ( bvult x (_ bv100 32) ) ( bvugt z (_ bv100 32) ) a!1 ) )) (inv x! z!))))
(assert (forall ((x (_ BitVec 32)) (z (_ BitVec 32))) 
       (=> (inv x z) ( or ( and ( bvult x (_ bv100 32) ) ( bvugt z (_ bv100 32) ) ) ( bvuge x (_ bv100 32) ) ( bvule z (_ bv100 32) ) ))))
(check-sat)
