(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (sn (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> ( and ( = sn (_ bv0 32) ) ( = x (_ bv0 32) ) ) (inv x sn v1 v2 v3))))
(assert (forall ((x (_ BitVec 32)) (sn (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32)) (x! (_ BitVec 32)) (sn! (_ BitVec 32)) (v1! (_ BitVec 32)) (v2! (_ BitVec 32)) (v3! (_ BitVec 32))) 
       (=> (and (inv x sn v1 v2 v3) ( and ( = x! ( bvadd x (_ bv1 32) ) ) ( = sn! ( bvadd sn (_ bv1 32) ) ) )) (inv x! sn! v1! v2! v3!))))
(assert (forall ((x (_ BitVec 32)) (sn (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> (inv x sn v1 v2 v3) ( or ( = sn x ) ( = sn ( bvadd (_ bv1 32) ( bvnot (_ bv1 32) ) ) ) ))))
(check-sat)
