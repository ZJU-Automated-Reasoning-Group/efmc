(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> ( and ( = x (_ bv0 64) ) ( = y (_ bv50 64) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64))) 
       (=> (and (inv x y) ( and ( bvslt x (_ bv100 64) ) ( ite ( bvslt x (_ bv50 64) ) ( = x! ( bvadd x (_ bv1 64) ) ) ( = y! y ) ) ( = x! ( bvadd x (_ bv1 64) ) ) ( = y! ( bvadd y (_ bv1 64) ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> (inv x y) ( or ( bvslt x (_ bv100 64) ) ( = y (_ bv100 64) ) ))))
(check-sat)
