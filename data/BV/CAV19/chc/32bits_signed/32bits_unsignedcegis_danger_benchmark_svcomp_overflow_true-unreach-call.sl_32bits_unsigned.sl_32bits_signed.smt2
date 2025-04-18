(set-logic HORN)
(declare-fun inv ((_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32))) 
       (=> ( = x #x0000000a ) (inv x))))
(assert (forall ((x (_ BitVec 32)) (x! (_ BitVec 32))) 
       (=> (and (inv x) ( and ( bvsge x #x0000000a ) ( = x! ( bvadd x #x00000002 ) ) )) (inv x!))))
(assert (forall ((x (_ BitVec 32))) 
       (=> (inv x) ( or ( = #x00000000 ( bvurem x #x00000002 ) ) ( bvsge x #x0000000a ) ))))
(check-sat)
