(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (n (_ BitVec 32)) (sn (_ BitVec 32))) 
       (=> ( and ( = i (_ bv1 32) ) ( = sn (_ bv0 32) ) ( bvsge n (_ bv0 32) ) ) (inv i n sn))))
(assert (forall ((i (_ BitVec 32)) (n (_ BitVec 32)) (sn (_ BitVec 32)) (i! (_ BitVec 32)) (n! (_ BitVec 32)) (sn! (_ BitVec 32))) 
       (=> (and (inv i n sn) ( and ( bvsle i n ) ( ite ( = i (_ bv4 32) ) ( = sn! ( bvsub (_ bv0 32) (_ bv10 32) ) ) ( = sn! ( bvadd sn (_ bv2 32) ) ) ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = n! n ) )) (inv i! n! sn!))))
(assert (forall ((i (_ BitVec 32)) (n (_ BitVec 32)) (sn (_ BitVec 32))) 
       (=> (inv i n sn) ( or ( bvsle i n ) ( = sn ( bvmul n (_ bv2 32) ) ) ( = sn (_ bv0 32) ) ))))
(check-sat)
