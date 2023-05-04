(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( and ( bvsle x (_ bv5 32) ) ( bvsge x (_ bv4 32) ) ( bvsle y (_ bv5 32) ) ( bvsge y (_ bv4 32) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv x y) ( or ( and ( = x! ( bvsub x (_ bv1 32) ) ) ( = y! y ) ( bvsge x (_ bv0 32) ) ( bvsge y (_ bv0 32) ) ) ( and ( = x! x ) ( = y! ( bvsub y (_ bv1 32) ) ) ( bvslt x (_ bv0 32) ) ( bvsge y (_ bv0 32) ) ) ( and ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! ( bvsub y (_ bv1 32) ) ) ( bvslt y (_ bv0 32) ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv x y) ( and ( bvsle y (_ bv5 32) ) ))))
(check-sat)