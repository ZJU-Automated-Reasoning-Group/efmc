(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( and ( = x #x00000001 ) ( = y #x00000000 ) ) (inv x y))))
(assert (forall ((x (_ BitVec 32)) (x! (_ BitVec 32)) (y (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv x x!) ( and ( bvslt y #x00000400 ) ( = x! #x00000000 ) ( = y! ( bvadd y #x00000001 ) ) )) (inv y y!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv x y) ( or ( = x #x00000000 ) ( bvslt y #x00000400 ) ))))
(check-sat)
