(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> ( = x (_ bv0 64) ) (inv x n))))
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64)) (x! (_ BitVec 64)) (n! (_ BitVec 64))) 
       (=> (and (inv x n) ( and ( = n! n ) ( bvult x n ) ( = x! ( bvadd x (_ bv1 64) ) ) )) (inv x! n!))))
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> (inv x n) ( or ( not ( bvuge x n ) ) ( = x n ) ( bvult n (_ bv0 64) ) ))))
(check-sat)
