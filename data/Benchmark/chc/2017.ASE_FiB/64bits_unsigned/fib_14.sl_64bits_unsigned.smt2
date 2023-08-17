(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((a (_ BitVec 64)) (j (_ BitVec 64)) (m (_ BitVec 64))) 
       (=> ( and ( = a (_ bv0 64) ) ( bvugt m (_ bv0 64) ) ( = j (_ bv1 64) ) ) (inv a j m))))
(assert (forall ((a (_ BitVec 64)) (j (_ BitVec 64)) (m (_ BitVec 64)) (a! (_ BitVec 64)) (j! (_ BitVec 64)) (m! (_ BitVec 64))) 
       (=> (and (inv a j m) ( or ( and ( bvugt j m ) ( = a! a ) ( = j! j ) ( = m! m ) ) ( and ( bvule j m ) ( = j! ( bvadd j (_ bv1 64) ) ) ( = a! ( bvadd a (_ bv1 64) ) ) ( = m! m ) ) ( and ( bvule j m ) ( = j! ( bvadd j (_ bv1 64) ) ) ( = a! ( bvsub a (_ bv1 64) ) ) ( = m! m ) ) )) (inv a! j! m!))))
(assert (forall ((a (_ BitVec 64)) (j (_ BitVec 64)) (m (_ BitVec 64))) 
       (=> (inv a j m) ( => ( not ( bvule j m ) ) ( and ( bvuge a ( bvsub (_ bv0 64) m ) ) ( bvule a m ) ) ))))
(check-sat)