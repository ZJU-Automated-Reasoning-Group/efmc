(set-logic HORN)
(declare-fun inv ((_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32))) 
       (=> ( = x #x0ffffff0 ) (inv x))))
(assert (forall ((x (_ BitVec 32)) (x! (_ BitVec 32))) 
       (=> (and (inv x) ( and ( bvsgt x #x00000000 ) ( = x! ( bvsub x #x00000002 ) ) )) (inv x!))))
(assert (forall ((x (_ BitVec 32))) 
       (=> (inv x) ( or ( = #x00000000 ( bvurem x #x00000002 ) ) ( bvsgt x #x00000000 ) ))))
(check-sat)