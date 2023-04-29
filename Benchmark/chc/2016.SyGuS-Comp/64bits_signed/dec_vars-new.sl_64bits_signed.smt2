(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64)) (v1 (_ BitVec 64)) (v2 (_ BitVec 64)) (v3 (_ BitVec 64))) 
       (=> ( = x n ) (inv x n v1 v2 v3))))
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64)) (v1 (_ BitVec 64)) (v2 (_ BitVec 64)) (v3 (_ BitVec 64)) (x! (_ BitVec 64)) (n! (_ BitVec 64)) (v1! (_ BitVec 64)) (v2! (_ BitVec 64)) (v3! (_ BitVec 64))) 
       (=> (and (inv x n v1 v2 v3) ( and ( bvsgt x (_ bv1 64) ) ( = x! ( bvsub x (_ bv1 64) ) ) ( = n! n ) )) (inv x! n! v1! v2! v3!))))
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64)) (v1 (_ BitVec 64)) (v2 (_ BitVec 64)) (v3 (_ BitVec 64))) 
       (=> (inv x n v1 v2 v3) ( not ( and ( bvsle x (_ bv1 64) ) ( not ( = x (_ bv1 64) ) ) ( bvsge n (_ bv0 64) ) ) ))))
(check-sat)
