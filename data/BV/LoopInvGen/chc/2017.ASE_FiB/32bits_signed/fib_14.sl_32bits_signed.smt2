(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((a (_ BitVec 32)) (j (_ BitVec 32)) (m (_ BitVec 32))) 
       (=> ( and ( = a (_ bv0 32) ) ( bvsgt m (_ bv0 32) ) ( = j (_ bv1 32) ) ) (inv a j m))))
(assert (forall ((a (_ BitVec 32)) (j (_ BitVec 32)) (m (_ BitVec 32)) (a! (_ BitVec 32)) (j! (_ BitVec 32)) (m! (_ BitVec 32))) 
       (=> (and (inv a j m) ( or ( and ( bvsgt j m ) ( = a! a ) ( = j! j ) ( = m! m ) ) ( and ( bvsle j m ) ( = j! ( bvadd j (_ bv1 32) ) ) ( = a! ( bvadd a (_ bv1 32) ) ) ( = m! m ) ) ( and ( bvsle j m ) ( = j! ( bvadd j (_ bv1 32) ) ) ( = a! ( bvsub a (_ bv1 32) ) ) ( = m! m ) ) )) (inv a! j! m!))))
(assert (forall ((a (_ BitVec 32)) (j (_ BitVec 32)) (m (_ BitVec 32))) 
       (=> (inv a j m) ( => ( not ( bvsle j m ) ) ( and ( bvsge a ( bvsub (_ bv0 32) m ) ) ( bvsle a m ) ) ))))
(check-sat)
