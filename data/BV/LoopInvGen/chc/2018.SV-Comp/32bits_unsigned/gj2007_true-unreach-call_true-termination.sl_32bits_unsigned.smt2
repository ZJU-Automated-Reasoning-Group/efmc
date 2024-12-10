(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( and ( = x (_ bv0 32) ) ( = y (_ bv50 32) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv x y) ( and ( bvult x (_ bv100 32) ) ( ite ( bvult x (_ bv50 32) ) ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! y ) ) ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! ( bvadd y (_ bv1 32) ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv x y) ( or ( bvult x (_ bv100 32) ) ( = y (_ bv100 32) ) ))))
(check-sat)