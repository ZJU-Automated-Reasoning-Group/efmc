(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (l (_ BitVec 64))) 
       (=> ( and ( = j (_ bv0 64) ) ( = i l ) ) (inv i j k l))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (l (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64)) (k! (_ BitVec 64)) (l! (_ BitVec 64))) 
       (=> (and (inv i j k l) ( and ( bvslt j (_ bv1000 64) ) ( = i! ( bvadd i k ) ) ( = j! ( bvadd j (_ bv1 64) ) ) ( = k! k ) ( = l! l ) )) (inv i! j! k! l!))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (l (_ BitVec 64))) 
       (=> (inv i j k l) ( or ( bvslt j (_ bv1000 64) ) ( = i ( bvadd l ( bvmul k j ) ) ) ))))
(check-sat)
