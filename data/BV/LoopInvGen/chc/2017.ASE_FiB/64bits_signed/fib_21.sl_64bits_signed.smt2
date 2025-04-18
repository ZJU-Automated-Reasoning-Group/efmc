(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (c1 (_ BitVec 64)) (c2 (_ BitVec 64)) (n (_ BitVec 64)) (v (_ BitVec 64))) 
       (=> ( and ( bvsgt n (_ bv0 64) ) ( bvslt n (_ bv10 64) ) ( = k (_ bv0 64) ) ( = i (_ bv0 64) ) ( = c1 (_ bv4000 64) ) ( = c2 (_ bv2000 64) ) ) (inv i j k c1 c2 n v))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (c1 (_ BitVec 64)) (c2 (_ BitVec 64)) (n (_ BitVec 64)) (v (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64)) (k! (_ BitVec 64)) (c1! (_ BitVec 64)) (c2! (_ BitVec 64)) (n! (_ BitVec 64)) (v! (_ BitVec 64))) 
       (=> (and (inv i j k c1 c2 n v) ( or ( and ( bvsge i n ) ( = i! i ) ( = j! j ) ( = k! k ) ( = c1! c1 ) ( = c2! c2 ) ( = n! n ) ( = v! v ) ) ( and ( bvslt i n ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = j! j ) ( = k! ( bvadd k c1 ) ) ( = c1! c1 ) ( = c2! c2 ) ( = n! n ) ( = v! (_ bv0 64) ) ) ( and ( bvslt i n ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = j! j ) ( = k! ( bvadd k c2 ) ) ( = c1! c1 ) ( = c2! c2 ) ( = n! n ) ( = v! (_ bv1 64) ) ) )) (inv i! j! k! c1! c2! n! v!))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (c1 (_ BitVec 64)) (c2 (_ BitVec 64)) (n (_ BitVec 64)) (v (_ BitVec 64))) 
       (=> (inv i j k c1 c2 n v) ( => ( bvsge i n ) ( bvsgt k n ) ))))
(check-sat)
