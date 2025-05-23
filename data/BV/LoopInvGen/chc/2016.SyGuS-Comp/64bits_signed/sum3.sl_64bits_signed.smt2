(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (sn (_ BitVec 64))) 
       (=> ( and ( = sn (_ bv0 64) ) ( = x (_ bv0 64) ) ) (inv x sn))))
(assert (forall ((x (_ BitVec 64)) (sn (_ BitVec 64)) (x! (_ BitVec 64)) (sn! (_ BitVec 64))) 
       (=> (and (inv x sn) ( and ( = x! ( bvadd x (_ bv1 64) ) ) ( = sn! ( bvadd sn (_ bv1 64) ) ) )) (inv x! sn!))))
(assert (forall ((x (_ BitVec 64)) (sn (_ BitVec 64))) 
       (=> (inv x sn) ( or ( = sn x ) ( = sn ( bvadd (_ bv1 64) ( bvnot (_ bv1 64) ) ) ) ))))
(check-sat)
