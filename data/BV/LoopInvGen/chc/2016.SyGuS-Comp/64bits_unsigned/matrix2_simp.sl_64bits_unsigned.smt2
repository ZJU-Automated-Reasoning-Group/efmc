(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((m (_ BitVec 64)) (a (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (r (_ BitVec 64)) (c (_ BitVec 64))) 
       (=> ( and ( or ( bvule a m ) ( = j (_ bv0 64) ) ) ( bvult j r ) ( = k (_ bv0 64) ) ) (inv m a j k r c))))
(assert (forall ((m (_ BitVec 64)) (a (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (r (_ BitVec 64)) (c (_ BitVec 64)) (m! (_ BitVec 64)) (a! (_ BitVec 64)) (j! (_ BitVec 64)) (k! (_ BitVec 64)) (r! (_ BitVec 64)) (c! (_ BitVec 64))) 
       (=> (and (inv m a j k r c) ( or ( and ( = j! j ) ( = r! r ) ( = c! c ) ( bvult k c ) ( bvult m a! ) ( = m! a! ) ( = k! ( bvadd k (_ bv1 64) ) ) ) ( and ( = j! j ) ( = r! r ) ( = c! c ) ( bvult k c ) ( bvugt m a! ) ( = k! ( bvadd k (_ bv1 64) ) ) ) )) (inv m! a! j! k! r! c!))))
(assert (forall ((m (_ BitVec 64)) (a (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (r (_ BitVec 64)) (c (_ BitVec 64))) 
       (=> (inv m a j k r c) ( or ( bvult k c ) ( bvule a m ) ( = j ( bvadd (_ bv1 64) ( bvnot (_ bv1 64) ) ) ) ))))
(check-sat)
