(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (n (_ BitVec 32)) (sn (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> ( and ( = sn (_ bv0 32) ) ( = i (_ bv1 32) ) ) (inv i n sn v1 v2 v3))))
(assert (forall ((i (_ BitVec 32)) (n (_ BitVec 32)) (sn (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32)) (i! (_ BitVec 32)) (n! (_ BitVec 32)) (sn! (_ BitVec 32)) (v1! (_ BitVec 32)) (v2! (_ BitVec 32)) (v3! (_ BitVec 32))) 
       (=> (and (inv i n sn v1 v2 v3) ( and ( = n! n ) ( = i! ( bvadd i (_ bv1 32) ) ) ( bvsle i n ) ( = sn! ( bvadd sn (_ bv1 32) ) ) )) (inv i! n! sn! v1! v2! v3!))))
(assert (forall ((i (_ BitVec 32)) (n (_ BitVec 32)) (sn (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> (inv i n sn v1 v2 v3) ( or ( bvsle i n ) ( = sn n ) ( = sn (_ bv0 32) ) ))))
(check-sat)
