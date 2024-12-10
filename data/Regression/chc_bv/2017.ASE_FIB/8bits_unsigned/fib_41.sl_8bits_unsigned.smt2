(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((n (_ BitVec 8)) (k (_ BitVec 8)) (i (_ BitVec 8)) (j (_ BitVec 8))) 
       (=> ( and ( = j (_ bv0 8) ) ( bvuge n (_ bv0 8) ) ( = i (_ bv0 8) ) ( or ( = k (_ bv1 8) ) ( bvuge k (_ bv0 8) ) ) ) (inv n k i j))))
(assert (forall ((n (_ BitVec 8)) (k (_ BitVec 8)) (i (_ BitVec 8)) (j (_ BitVec 8)) (n! (_ BitVec 8)) (k! (_ BitVec 8)) (i! (_ BitVec 8)) (j! (_ BitVec 8))) 
       (=> (and (inv n k i j) ( or ( and ( bvugt i n ) ( = n! n ) ( = k! k ) ( = i! i ) ( = j! j ) ) ( and ( bvule i n ) ( = n! n ) ( = k! k ) ( = i! ( bvadd i (_ bv1 8) ) ) ( = j! ( bvadd j (_ bv1 8) ) ) ) )) (inv n! k! i! j!))))
(assert (forall ((n (_ BitVec 8)) (k (_ BitVec 8)) (i (_ BitVec 8)) (j (_ BitVec 8))) 
       (=> (inv n k i j) ( => ( bvugt i n ) ( bvugt ( bvadd k i j ) ( bvmul (_ bv2 8) n ) ) ))))
(check-sat)