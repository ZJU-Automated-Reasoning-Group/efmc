(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((m (_ BitVec 32)) (a (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> ( and ( or ( bvsle a m ) ( = j (_ bv0 32) ) ) ( bvslt j (_ bv1 32) ) ( = k (_ bv0 32) ) ) (inv m a j k))))
(assert (forall ((m (_ BitVec 32)) (a (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32)) (m! (_ BitVec 32)) (a! (_ BitVec 32)) (j! (_ BitVec 32)) (k! (_ BitVec 32))) 
       (=> (and (inv m a j k) ( or ( and ( = j! j ) ( bvslt k (_ bv1 32) ) ( bvslt m a! ) ( = m! a! ) ( = k! ( bvadd k (_ bv1 32) ) ) ) ( and ( = j! j ) ( bvslt k (_ bv1 32) ) ( bvsgt m a! ) ( = k! ( bvadd k (_ bv1 32) ) ) ) )) (inv m! a! j! k!))))
(assert (forall ((m (_ BitVec 32)) (a (_ BitVec 32)) (j (_ BitVec 32)) (k (_ BitVec 32))) 
       (=> (inv m a j k) ( or ( bvslt k (_ bv1 32) ) ( bvslt a m ) ( = j ( bvadd (_ bv1 32) ( bvnot (_ bv1 32) ) ) ) ))))
(check-sat)
