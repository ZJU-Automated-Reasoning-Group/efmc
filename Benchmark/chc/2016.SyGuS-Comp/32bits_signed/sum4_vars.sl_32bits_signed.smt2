(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (sn (_ BitVec 32)) (size (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> ( and ( = sn (_ bv0 32) ) ( = i (_ bv1 32) ) ) (inv i sn size v1 v2 v3))))
(assert (forall ((i (_ BitVec 32)) (sn (_ BitVec 32)) (size (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32)) (i! (_ BitVec 32)) (sn! (_ BitVec 32)) (size! (_ BitVec 32)) (v1! (_ BitVec 32)) (v2! (_ BitVec 32)) (v3! (_ BitVec 32))) 
       (=> (and (inv i sn size v1 v2 v3) ( and ( = size! size ) ( = i! ( bvadd i (_ bv1 32) ) ) ( bvsle i size ) ( = sn! ( bvadd sn (_ bv1 32) ) ) )) (inv i! sn! size! v1! v2! v3!))))
(assert (forall ((i (_ BitVec 32)) (sn (_ BitVec 32)) (size (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> (inv i sn size v1 v2 v3) ( or ( bvsle i size ) ( = sn size ) ( = sn (_ bv0 32) ) ))))
(check-sat)
