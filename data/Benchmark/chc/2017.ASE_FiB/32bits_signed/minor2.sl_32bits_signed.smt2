(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( and ( bvsle x (_ bv1 32) ) ( bvsge x (_ bv0 32) ) ( = y ( bvadd (_ bv1 32) ( bvnot (_ bv3 32) ) ) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv x y) ( or ( and ( = x! ( bvsub x (_ bv1 32) ) ) ( = y! ( bvadd y (_ bv2 32) ) ) ( bvslt ( bvsub x y ) (_ bv2 32) ) ) ( and ( = x! x ) ( = y! ( bvadd y (_ bv1 32) ) ) ( bvsge ( bvsub x y ) (_ bv2 32) ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv x y) ( and ( bvsle x (_ bv1 32) ) ( bvsge y ( bvadd (_ bv1 32) ( bvnot (_ bv3 32) ) ) ) ))))
(check-sat)
