(set-logic HORN)
(declare-fun inv ((_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64))) 
       (=> ( = x x ) (inv x))))
(assert (forall ((x (_ BitVec 64)) (x! (_ BitVec 64))) 
       (=> (and (inv x) ( and ( bvult x #x0fffffff ) ( = x! ( bvadd x #x00000001 ) ) )) (inv x!))))
(assert (forall ((x (_ BitVec 64))) 
       (=> (inv x) ( or ( bvuge x #x0fffffff ) ( bvult x #x0fffffff ) ))))
(check-sat)
