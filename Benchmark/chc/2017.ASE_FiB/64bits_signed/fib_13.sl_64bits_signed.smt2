(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((j (_ BitVec 64)) (k (_ BitVec 64)) (t (_ BitVec 64))) 
       (=> ( and ( = j (_ bv2 64) ) ( = k (_ bv0 64) ) ) (inv j k t))))
(assert (forall ((j (_ BitVec 64)) (k (_ BitVec 64)) (t (_ BitVec 64)) (j! (_ BitVec 64)) (k! (_ BitVec 64)) (t! (_ BitVec 64))) 
       (=> (and (inv j k t) ( or ( and ( = t (_ bv0 64) ) ( = j! ( bvadd j (_ bv4 64) ) ) ( = k! k ) ( = t! t ) ) ( and ( not ( = t (_ bv0 64) ) ) ( = j! ( bvadd j (_ bv2 64) ) ) ( = k! ( bvadd k (_ bv1 64) ) ) ( = t! t ) ) )) (inv j! k! t!))))
(assert (forall ((j (_ BitVec 64)) (k (_ BitVec 64)) (t (_ BitVec 64))) 
       (=> (inv j k t) ( or ( = k (_ bv0 64) ) ( = j ( bvadd ( bvmul k (_ bv2 64) ) (_ bv2 64) ) ) ))))
(check-sat)
