(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((i (_ BitVec 8)) (j (_ BitVec 8)) (n (_ BitVec 8)) (k (_ BitVec 8))) 
       (=> ( and ( or ( = n (_ bv1 8) ) ( = n (_ bv2 8) ) ) ( = i (_ bv0 8) ) ( = j (_ bv0 8) ) ) (inv i j n k))))
(assert (forall ((i (_ BitVec 8)) (j (_ BitVec 8)) (n (_ BitVec 8)) (k (_ BitVec 8)) (i! (_ BitVec 8)) (j! (_ BitVec 8)) (n! (_ BitVec 8)) (k! (_ BitVec 8))) 
       (=> (and (inv i j n k) ( or ( and ( bvugt i k ) ( = i! i ) ( = j! j ) ( = n! n ) ( = k! k ) ) ( and ( bvule i k ) ( = i! ( bvadd i (_ bv1 8) ) ) ( = j! ( bvadd j n ) ) ( = n! n ) ( = k! k ) ) )) (inv i! j! n! k!))))
(assert (forall ((i (_ BitVec 8)) (j (_ BitVec 8)) (n (_ BitVec 8)) (k (_ BitVec 8))) 
       (=> (inv i j n k) ( => ( bvugt i k ) ( or ( not ( = n (_ bv1 8) ) ) ( = i j ) ) ))))
(check-sat)
