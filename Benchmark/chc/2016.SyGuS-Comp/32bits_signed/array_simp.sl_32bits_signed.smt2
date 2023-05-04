(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (size (_ BitVec 32))) 
       (=> ( = x (_ bv0 32) ) (inv x y z size))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (size (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (z! (_ BitVec 32)) (size! (_ BitVec 32))) 
       (=> (and (inv x y z size) ( or ( and ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! z! ) ( bvsle z! y ) ( bvslt x size ) ) ( and ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! y ) ( bvsgt z! y ) ( bvslt x size ) ) )) (inv x! y! z! size!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (size (_ BitVec 32))) 
       (=> (inv x y z size) ( not ( and ( bvsge x size ) ( bvslt z y ) ( bvsgt size (_ bv0 32) ) ) ))))
(check-sat)