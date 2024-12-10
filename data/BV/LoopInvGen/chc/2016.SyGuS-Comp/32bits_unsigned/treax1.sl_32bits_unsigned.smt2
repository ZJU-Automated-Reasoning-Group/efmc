(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( = x (_ bv1 32) ) (inv x y))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv x y) ( and ( bvult x y ) ( = x! ( bvadd x x ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv x y) ( or ( not ( bvuge x y ) ) ( bvuge x (_ bv1 32) ) ))))
(check-sat)