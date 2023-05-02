(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> ( and ( = x (_ bv0 64) ) ( = y (_ bv0 64) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64))) 
       (=> (and (inv x y) ( or ( and ( = x! ( bvadd x (_ bv1 64) ) ) ( = y! ( bvadd y (_ bv100 64) ) ) ) ( and ( bvuge x (_ bv4 64) ) ( = x! ( bvadd x (_ bv1 64) ) ) ( = y! ( bvadd y (_ bv1 64) ) ) ) ( and ( bvult x (_ bv0 64) ) ( = x! x ) ( = y! ( bvsub y (_ bv1 64) ) ) ) ( and ( = x! x ) ( = y! y ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> (inv x y) ( or ( bvult x (_ bv4 64) ) ( bvugt y (_ bv2 64) ) ))))
(check-sat)
