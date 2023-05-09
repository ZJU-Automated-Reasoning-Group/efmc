(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((n (_ BitVec 8)) (m (_ BitVec 8)) (x (_ BitVec 8)) (y (_ BitVec 8))) 
       (=> ( and ( bvsge n (_ bv0 8) ) ( bvsge m (_ bv0 8) ) ( bvslt m n ) ( = x (_ bv0 8) ) ( = y m ) ) (inv n m x y))))
(assert (forall ((n (_ BitVec 8)) (m (_ BitVec 8)) (x (_ BitVec 8)) (y (_ BitVec 8)) (n! (_ BitVec 8)) (m! (_ BitVec 8)) (x! (_ BitVec 8)) (y! (_ BitVec 8))) 
       (=> (and (inv n m x y) ( or ( and ( bvslt x n ) ( bvsle ( bvadd x (_ bv1 8) ) m ) ( = x! ( bvadd x (_ bv1 8) ) ) ( = y! y ) ( = n! n ) ( = m! m ) ) ( and ( bvslt x n ) ( bvsgt ( bvadd x (_ bv1 8) ) m ) ( = x! ( bvadd x (_ bv1 8) ) ) ( = y! ( bvadd y (_ bv1 8) ) ) ( = n! n ) ( = m! m ) ) ( and ( bvsge x n ) ( = x! x ) ( = y! y ) ( = n! n ) ( = m! m ) ) )) (inv n! m! x! y!))))
(assert (forall ((n (_ BitVec 8)) (m (_ BitVec 8)) (x (_ BitVec 8)) (y (_ BitVec 8))) 
       (=> (inv n m x y) ( => ( not ( bvslt x n ) ) ( = y n ) ))))
(check-sat)
