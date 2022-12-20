(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((a (_ BitVec 8)) (j (_ BitVec 8)) (m (_ BitVec 8))) 
       (=> ( and ( = a (_ bv0 8) ) ( bvsgt m (_ bv0 8) ) ( = j (_ bv1 8) ) ) (inv a j m))))
(assert (forall ((a (_ BitVec 8)) (j (_ BitVec 8)) (m (_ BitVec 8)) (a! (_ BitVec 8)) (j! (_ BitVec 8)) (m! (_ BitVec 8))) 
       (=> (and (inv a j m) ( or ( and ( bvsgt j m ) ( = a! a ) ( = j! j ) ( = m! m ) ) ( and ( bvsle j m ) ( = j! ( bvadd j (_ bv1 8) ) ) ( = a! ( bvadd a (_ bv1 8) ) ) ( = m! m ) ) ( and ( bvsle j m ) ( = j! ( bvadd j (_ bv1 8) ) ) ( = a! ( bvsub a (_ bv1 8) ) ) ( = m! m ) ) )) (inv a! j! m!))))
(assert (forall ((a (_ BitVec 8)) (j (_ BitVec 8)) (m (_ BitVec 8))) 
       (=> (inv a j m) ( => ( not ( bvsle j m ) ) ( and ( bvsge a ( bvsub (_ bv0 8) m ) ) ( bvsle a m ) ) ))))
(check-sat)
