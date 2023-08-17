(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> ( = x #x00000001 ) (inv x y))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64))) 
       (=> (and (inv x y) ( let ( ( a!1 ( or ( and ( bvsgt x #x00000000 ) ( bvslt x ( bvudiv y x ) ) ( = x! ( bvmul x x ) ) ) ( = x! ( bvadd x #x00000001 ) ) ) ) ) ( and ( bvsgt y #x00000000 ) ( bvslt x y ) ( = y! y ) a!1 ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> (inv x y) ( or ( = y #x00000000 ) ( = x y ) ( and ( bvslt y #x00000000 ) ( bvslt x y ) ) ))))
(check-sat)