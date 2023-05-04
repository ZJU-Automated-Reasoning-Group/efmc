(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (N (_ BitVec 32))) 
       (=> ( and ( = x #x00000000 ) ( = N ( bvurem N #x0000ffff ) ) ) (inv x N))))
(assert (forall ((x (_ BitVec 32)) (N (_ BitVec 32)) (x! (_ BitVec 32)) (N! (_ BitVec 32))) 
       (=> (and (inv x N) ( and ( bvslt x N ) ( = x! ( bvadd x #x00000002 ) ) ( = N! N ) )) (inv x! N!))))
(assert (forall ((x (_ BitVec 32)) (N (_ BitVec 32))) 
       (=> (inv x N) ( or ( = #x00000000 ( bvurem x #x00000002 ) ) ( bvslt x N ) ))))
(check-sat)
