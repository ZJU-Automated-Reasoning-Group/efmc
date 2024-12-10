(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((j (_ BitVec 32)) (k (_ BitVec 32)) (t (_ BitVec 32))) 
       (=> ( and ( = j (_ bv2 32) ) ( = k (_ bv0 32) ) ) (inv j k t))))
(assert (forall ((j (_ BitVec 32)) (k (_ BitVec 32)) (t (_ BitVec 32)) (j! (_ BitVec 32)) (k! (_ BitVec 32)) (t! (_ BitVec 32))) 
       (=> (and (inv j k t) ( or ( and ( = t (_ bv0 32) ) ( = j! ( bvadd j (_ bv4 32) ) ) ( = k! k ) ( = t! t ) ) ( and ( not ( = t (_ bv0 32) ) ) ( = j! ( bvadd j (_ bv2 32) ) ) ( = k! ( bvadd k (_ bv1 32) ) ) ( = t! t ) ) )) (inv j! k! t!))))
(assert (forall ((j (_ BitVec 32)) (k (_ BitVec 32)) (t (_ BitVec 32))) 
       (=> (inv j k t) ( or ( = k (_ bv0 32) ) ( = j ( bvadd ( bvmul k (_ bv2 32) ) (_ bv2 32) ) ) ))))
(check-sat)