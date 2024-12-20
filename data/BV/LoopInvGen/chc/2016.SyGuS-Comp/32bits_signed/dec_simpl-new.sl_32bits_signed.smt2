(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> ( = x n ) (inv x n))))
(assert (forall ((x (_ BitVec 32)) (n (_ BitVec 32)) (x! (_ BitVec 32)) (n! (_ BitVec 32))) 
       (=> (and (inv x n) ( and ( bvsgt x (_ bv1 32) ) ( = x! ( bvsub x (_ bv1 32) ) ) ( = n! n ) )) (inv x! n!))))
(assert (forall ((x (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> (inv x n) ( not ( and ( bvsle x (_ bv1 32) ) ( not ( = x (_ bv1 32) ) ) ( bvsge n (_ bv0 32) ) ) ))))
(check-sat)
