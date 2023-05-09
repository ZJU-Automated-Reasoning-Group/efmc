(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((n (_ BitVec 8)) (m (_ BitVec 8)) (x (_ BitVec 8)) (y (_ BitVec 8))) 
       (=> ( and ( bvuge n (_ bv0 8) ) ( bvuge m (_ bv0 8) ) ( bvult m n ) ( = x (_ bv0 8) ) ( = y m ) ) (inv n m x y))))
(assert (forall ((n (_ BitVec 8)) (m (_ BitVec 8)) (x (_ BitVec 8)) (y (_ BitVec 8)) (n! (_ BitVec 8)) (m! (_ BitVec 8)) (x! (_ BitVec 8)) (y! (_ BitVec 8))) 
       (=> (and (inv n m x y) ( or ( and ( bvult x n ) ( bvule ( bvadd x (_ bv1 8) ) m ) ( = x! ( bvadd x (_ bv1 8) ) ) ( = y! y ) ( = n! n ) ( = m! m ) ) ( and ( bvult x n ) ( bvugt ( bvadd x (_ bv1 8) ) m ) ( = x! ( bvadd x (_ bv1 8) ) ) ( = y! ( bvadd y (_ bv1 8) ) ) ( = n! n ) ( = m! m ) ) ( and ( bvuge x n ) ( = x! x ) ( = y! y ) ( = n! n ) ( = m! m ) ) )) (inv n! m! x! y!))))
(assert (forall ((n (_ BitVec 8)) (m (_ BitVec 8)) (x (_ BitVec 8)) (y (_ BitVec 8))) 
       (=> (inv n m x y) ( => ( not ( bvult x n ) ) ( = y n ) ))))
(check-sat)
