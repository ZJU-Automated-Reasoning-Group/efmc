(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8))) 
       (=> ( and ( bvule x (_ bv5 8) ) ( bvuge x (_ bv4 8) ) ( bvule y (_ bv5 8) ) ( bvuge y (_ bv4 8) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (x! (_ BitVec 8)) (y! (_ BitVec 8))) 
       (=> (and (inv x y) ( or ( and ( = x! ( bvsub x (_ bv1 8) ) ) ( = y! y ) ( bvuge x (_ bv0 8) ) ( bvuge y (_ bv0 8) ) ) ( and ( = x! x ) ( = y! ( bvsub y (_ bv1 8) ) ) ( bvult x (_ bv0 8) ) ( bvuge y (_ bv0 8) ) ) ( and ( = x! ( bvadd x (_ bv1 8) ) ) ( = y! ( bvsub y (_ bv1 8) ) ) ( bvult y (_ bv0 8) ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8))) 
       (=> (inv x y) ( and ( bvule y (_ bv5 8) ) ))))
(check-sat)
