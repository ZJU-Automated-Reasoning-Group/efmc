(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (sn (_ BitVec 32)) (size (_ BitVec 32))) 
       (=> ( and ( = sn (_ bv0 32) ) ( = i (_ bv1 32) ) ) (inv i sn size))))
(assert (forall ((i (_ BitVec 32)) (sn (_ BitVec 32)) (size (_ BitVec 32)) (i! (_ BitVec 32)) (sn! (_ BitVec 32)) (size! (_ BitVec 32))) 
       (=> (and (inv i sn size) ( and ( = size! size ) ( = i! ( bvadd i (_ bv1 32) ) ) ( bvule i size ) ( = sn! ( bvadd sn (_ bv1 32) ) ) )) (inv i! sn! size!))))
(assert (forall ((i (_ BitVec 32)) (sn (_ BitVec 32)) (size (_ BitVec 32))) 
       (=> (inv i sn size) ( or ( bvule i size ) ( = sn size ) ( = sn (_ bv0 32) ) ))))
(check-sat)