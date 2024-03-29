(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> ( and ( bvule x (_ bv1 64) ) ( bvuge x (_ bv0 64) ) ( = y ( bvadd (_ bv1 64) ( bvnot (_ bv3 64) ) ) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64))) 
       (=> (and (inv x y) ( or ( and ( = x! ( bvsub x (_ bv1 64) ) ) ( = y! ( bvadd y (_ bv2 64) ) ) ( bvult ( bvsub x y ) (_ bv2 64) ) ) ( and ( = x! x ) ( = y! ( bvadd y (_ bv1 64) ) ) ( bvuge ( bvsub x y ) (_ bv2 64) ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> (inv x y) ( and ( bvule x (_ bv1 64) ) ( bvuge y ( bvadd (_ bv1 64) ( bvnot (_ bv3 64) ) ) ) ))))
(check-sat)
