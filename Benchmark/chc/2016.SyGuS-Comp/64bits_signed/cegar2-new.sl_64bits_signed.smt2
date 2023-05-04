(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64)) (m (_ BitVec 64))) 
       (=> ( and ( = x (_ bv1 64) ) ( = m (_ bv1 64) ) ) (inv x n m))))
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64)) (m (_ BitVec 64)) (x! (_ BitVec 64)) (n! (_ BitVec 64)) (m! (_ BitVec 64))) 
       (=> (and (inv x n m) ( let ( ( a!1 ( and ( bvslt x n ) ( = x! ( bvadd x (_ bv1 64) ) ) ( = n! n ) ) ) ) ( or ( and a!1 ( = m! m ) ) ( and a!1 ( = m! x ) ) ) )) (inv x! n! m!))))
(assert (forall ((x (_ BitVec 64)) (n (_ BitVec 64)) (m (_ BitVec 64))) 
       (=> (inv x n m) ( not ( and ( bvsge x n ) ( bvsgt n (_ bv1 64) ) ( or ( bvsle n m ) ( bvslt m (_ bv1 64) ) ) ) ))))
(check-sat)