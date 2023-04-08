(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8))) 
       (=> ( and ( = x (_ bv1 8) ) ( = y (_ bv1 8) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (x! (_ BitVec 8)) (y! (_ BitVec 8))) 
       (=> (and (inv x y) ( and ( = x! ( bvadd x y ) ) ( = y! ( bvadd x y ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8))) 
       (=> (inv x y) ( bvsge y (_ bv1 8) ))))
(check-sat)