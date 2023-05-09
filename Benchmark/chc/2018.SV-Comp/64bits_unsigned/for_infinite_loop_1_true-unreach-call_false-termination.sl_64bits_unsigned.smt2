(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> ( and ( = i (_ bv0 64) ) ( = x (_ bv0 64) ) ( = y (_ bv0 64) ) ( bvugt n (_ bv0 64) ) ) (inv i x y n))))
(assert (forall ((i (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (n (_ BitVec 64)) (i! (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (n! (_ BitVec 64))) 
       (=> (and (inv i x y n) ( and ( = i! ( bvadd i (_ bv1 64) ) ) ( = x! x ) ( = y! y ) ( = n! n ) )) (inv i! x! y! n!))))
(assert (forall ((i (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> (inv i x y n) ( = x (_ bv0 64) ))))
(check-sat)
