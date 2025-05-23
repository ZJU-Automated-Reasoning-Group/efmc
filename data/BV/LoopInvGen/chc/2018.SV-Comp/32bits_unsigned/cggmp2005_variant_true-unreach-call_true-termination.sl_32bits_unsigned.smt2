(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((lo (_ BitVec 32)) (mid (_ BitVec 32)) (hi (_ BitVec 32))) 
       (=> ( and ( = lo (_ bv0 32) ) ( bvugt mid (_ bv0 32) ) ( = hi ( bvmul (_ bv2 32) mid ) ) ) (inv lo mid hi))))
(assert (forall ((lo (_ BitVec 32)) (mid (_ BitVec 32)) (hi (_ BitVec 32)) (lo! (_ BitVec 32)) (mid! (_ BitVec 32)) (hi! (_ BitVec 32))) 
       (=> (and (inv lo mid hi) ( and ( bvugt mid (_ bv0 32) ) ( = lo! ( bvadd lo (_ bv1 32) ) ) ( = hi! ( bvsub hi (_ bv1 32) ) ) ( = mid! ( bvsub mid (_ bv1 32) ) ) )) (inv lo! mid! hi!))))
(assert (forall ((lo (_ BitVec 32)) (mid (_ BitVec 32)) (hi (_ BitVec 32))) 
       (=> (inv lo mid hi) ( or ( bvugt mid (_ bv0 32) ) ( = lo hi ) ))))
(check-sat)
