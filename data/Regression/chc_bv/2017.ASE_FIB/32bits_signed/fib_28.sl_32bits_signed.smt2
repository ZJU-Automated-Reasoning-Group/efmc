(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((n (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( and ( = n (_ bv0 32) ) ( bvsge x (_ bv0 32) ) ( bvsge y (_ bv0 32) ) ( = x y ) ) (inv n x y))))
(assert (forall ((n (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (n! (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv n x y) ( or ( and ( = x n ) ( = n! n ) ( = x! x ) ( = y! y ) ) ( and ( not ( = x n ) ) ( = n! n ) ( = x! ( bvsub x (_ bv1 32) ) ) ( = y! ( bvsub y (_ bv1 32) ) ) ) )) (inv n! x! y!))))
(assert (forall ((n (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv n x y) ( => ( = x n ) ( = y n ) ))))
(check-sat)
