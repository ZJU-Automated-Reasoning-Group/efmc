(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( = x ( bvadd (_ bv1 32) ( bvnot (_ bv50 32) ) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv x y) ( or ( and ( bvslt x (_ bv0 32) ) ( = x! ( bvadd x y ) ) ( = y! ( bvadd y (_ bv1 32) ) ) ) ( and ( bvsge x (_ bv0 32) ) ( = x! x ) ( = y! y ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv x y) ( => ( not ( bvslt x (_ bv0 32) ) ) ( bvsge y (_ bv0 32) ) ))))
(check-sat)