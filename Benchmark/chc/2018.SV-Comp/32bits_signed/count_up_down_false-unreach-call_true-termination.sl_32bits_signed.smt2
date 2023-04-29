(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((n (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( and ( = y (_ bv0 32) ) ( = x n ) ) (inv n x y))))
(assert (forall ((n (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (n! (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv n x y) ( and ( bvsgt x (_ bv0 32) ) ( = x! ( bvsub x (_ bv1 32) ) ) ( = y! ( bvadd y (_ bv1 32) ) ) ( = n! n ) )) (inv n! x! y!))))
(assert (forall ((n (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv n x y) ( or ( bvsgt x (_ bv0 32) ) ( = y n ) ))))
(check-sat)
