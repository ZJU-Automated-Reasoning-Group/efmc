(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((n (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> ( and ( = n (_ bv0 64) ) ( bvsge x (_ bv0 64) ) ( bvsge y (_ bv0 64) ) ( = x y ) ) (inv n x y))))
(assert (forall ((n (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (n! (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64))) 
       (=> (and (inv n x y) ( or ( and ( = x n ) ( = n! n ) ( = x! x ) ( = y! y ) ) ( and ( not ( = x n ) ) ( = n! n ) ( = x! ( bvsub x (_ bv1 64) ) ) ( = y! ( bvsub y (_ bv1 64) ) ) ) )) (inv n! x! y!))))
(assert (forall ((n (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64))) 
       (=> (inv n x y) ( => ( = x n ) ( = y n ) ))))
(check-sat)
