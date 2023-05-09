(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (m (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> ( and ( = x (_ bv0 32) ) ( = m (_ bv0 32) ) ( bvsgt n (_ bv0 32) ) ) (inv x m n))))
(assert (forall ((x (_ BitVec 32)) (m (_ BitVec 32)) (n (_ BitVec 32)) (x! (_ BitVec 32)) (m! (_ BitVec 32)) (n! (_ BitVec 32))) 
       (=> (and (inv x m n) ( or ( and ( bvsge x n ) ( = x! x ) ( = m! m ) ( = n! n ) ) ( and ( bvslt x n ) ( = x! ( bvadd x (_ bv1 32) ) ) ( = m! x ) ( = n! n ) ) ( and ( bvslt x n ) ( = x! ( bvadd x (_ bv1 32) ) ) ( = m! m ) ( = n! n ) ) )) (inv x! m! n!))))
(assert (forall ((x (_ BitVec 32)) (m (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> (inv x m n) ( => ( bvsge x n ) ( or ( bvsle n (_ bv0 32) ) ( and ( bvsle (_ bv0 32) m ) ( bvslt m n ) ) ) ))))
(check-sat)
