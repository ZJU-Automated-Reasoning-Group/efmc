(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> ( and ( = x #x00000000 ) ( = y #x00000001 ) ) (inv x y))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64))) 
       (=> (and (inv x y) ( and ( bvslt x #x00000006 ) ( = x! ( bvadd x #x00000001 ) ) ( = y! ( bvmul y #x00000002 ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> (inv x y) ( or ( = #x00000006 x ) ( bvslt x #x00000006 ) ))))
(check-sat)
