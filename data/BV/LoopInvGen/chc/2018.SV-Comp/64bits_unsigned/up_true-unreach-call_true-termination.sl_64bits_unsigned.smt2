(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((n (_ BitVec 64)) (i (_ BitVec 64)) (k (_ BitVec 64)) (j (_ BitVec 64))) 
       (=> ( and ( = i (_ bv0 64) ) ( = k (_ bv0 64) ) ( = j (_ bv0 64) ) ) (inv n i k j))))
(assert (forall ((n (_ BitVec 64)) (i (_ BitVec 64)) (k (_ BitVec 64)) (j (_ BitVec 64)) (n! (_ BitVec 64)) (i! (_ BitVec 64)) (k! (_ BitVec 64)) (j! (_ BitVec 64))) 
       (=> (and (inv n i k j) ( or ( and ( bvult i n ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = k! ( bvadd k (_ bv1 64) ) ) ( = n! n ) ( = j! j ) ) ( and ( bvuge i n ) ( bvult j n ) ( = j! ( bvadd j (_ bv1 64) ) ) ( = k! ( bvsub k (_ bv1 64) ) ) ( = n! n ) ( = i! i ) ) )) (inv n! i! k! j!))))
(assert (forall ((n (_ BitVec 64)) (i (_ BitVec 64)) (k (_ BitVec 64)) (j (_ BitVec 64))) 
       (=> (inv n i k j) ( or ( not ( and ( bvuge i n ) ( bvult j n ) ) ) ( bvugt k (_ bv0 64) ) ))))
(check-sat)
