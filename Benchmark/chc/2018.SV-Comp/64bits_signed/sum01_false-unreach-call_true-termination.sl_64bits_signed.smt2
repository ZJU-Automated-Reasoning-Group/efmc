(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (n (_ BitVec 64)) (sn (_ BitVec 64))) 
       (=> ( and ( = i (_ bv1 64) ) ( = sn (_ bv0 64) ) ( bvsge n (_ bv0 64) ) ) (inv i n sn))))
(assert (forall ((i (_ BitVec 64)) (n (_ BitVec 64)) (sn (_ BitVec 64)) (i! (_ BitVec 64)) (n! (_ BitVec 64)) (sn! (_ BitVec 64))) 
       (=> (and (inv i n sn) ( and ( bvsle i n ) ( ite ( bvslt i (_ bv10 64) ) ( = sn! ( bvadd sn (_ bv2 64) ) ) ( = sn! sn ) ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = n! n ) )) (inv i! n! sn!))))
(assert (forall ((i (_ BitVec 64)) (n (_ BitVec 64)) (sn (_ BitVec 64))) 
       (=> (inv i n sn) ( or ( bvsle i n ) ( = sn ( bvmul n (_ bv2 64) ) ) ( = sn (_ bv0 64) ) ))))
(check-sat)
