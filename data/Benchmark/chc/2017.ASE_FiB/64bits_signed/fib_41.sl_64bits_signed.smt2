(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((n (_ BitVec 64)) (k (_ BitVec 64)) (i (_ BitVec 64)) (j (_ BitVec 64))) 
       (=> ( and ( = j (_ bv0 64) ) ( bvsge n (_ bv0 64) ) ( = i (_ bv0 64) ) ( or ( = k (_ bv1 64) ) ( bvsge k (_ bv0 64) ) ) ) (inv n k i j))))
(assert (forall ((n (_ BitVec 64)) (k (_ BitVec 64)) (i (_ BitVec 64)) (j (_ BitVec 64)) (n! (_ BitVec 64)) (k! (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64))) 
       (=> (and (inv n k i j) ( or ( and ( bvsgt i n ) ( = n! n ) ( = k! k ) ( = i! i ) ( = j! j ) ) ( and ( bvsle i n ) ( = n! n ) ( = k! k ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = j! ( bvadd j (_ bv1 64) ) ) ) )) (inv n! k! i! j!))))
(assert (forall ((n (_ BitVec 64)) (k (_ BitVec 64)) (i (_ BitVec 64)) (j (_ BitVec 64))) 
       (=> (inv n k i j) ( => ( bvsgt i n ) ( bvsgt ( bvadd k i j ) ( bvmul (_ bv2 64) n ) ) ))))
(check-sat)