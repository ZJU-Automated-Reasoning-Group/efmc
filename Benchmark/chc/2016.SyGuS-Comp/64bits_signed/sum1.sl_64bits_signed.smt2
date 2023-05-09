(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (n (_ BitVec 64)) (sn (_ BitVec 64))) 
       (=> ( and ( = sn (_ bv0 64) ) ( = i (_ bv1 64) ) ) (inv i n sn))))
(assert (forall ((i (_ BitVec 64)) (n (_ BitVec 64)) (sn (_ BitVec 64)) (i! (_ BitVec 64)) (n! (_ BitVec 64)) (sn! (_ BitVec 64))) 
       (=> (and (inv i n sn) ( and ( = n! n ) ( = i! ( bvadd i (_ bv1 64) ) ) ( bvsle i n ) ( = sn! ( bvadd sn (_ bv1 64) ) ) )) (inv i! n! sn!))))
(assert (forall ((i (_ BitVec 64)) (n (_ BitVec 64)) (sn (_ BitVec 64))) 
       (=> (inv i n sn) ( or ( bvsle i n ) ( = sn n ) ( = sn (_ bv0 64) ) ))))
(check-sat)
