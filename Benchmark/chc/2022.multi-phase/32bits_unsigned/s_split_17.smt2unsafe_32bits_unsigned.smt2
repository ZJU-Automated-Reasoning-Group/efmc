(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((v (_ BitVec 32))
         (x (_ BitVec 32))
         (z (_ BitVec 32))
         (w (_ BitVec 32)))
  (=> (and (bvugt x z) (= v #x00000000) (= w #x00000000)) (inv v x z w))))
(assert (forall ((v (_ BitVec 32))
         (x (_ BitVec 32))
         (z (_ BitVec 32))
         (w (_ BitVec 32))
         (x! (_ BitVec 32))
         (z! (_ BitVec 32))
         (v! (_ BitVec 32))
         (w! (_ BitVec 32)))
  (let ((a!1 (and (inv v x z w)
                  (= x! (bvadd x #x00000001))
                  (= z! (bvadd z #x00000002))
                  (= v! (ite (bvult x z) (bvadd v #x00000001) v))
                  (= w! (ite (bvult x z) w (bvadd w #x00000001))))))
    (=> a!1 (inv x! z! v! w!)))))
(assert (forall ((v (_ BitVec 32))
         (x (_ BitVec 32))
         (z (_ BitVec 32))
         (w (_ BitVec 32)))
  (let ((a!1 (not (and (not (bvule v #x000003e8)) (not (bvule w #x00000000))))))
    (=> (inv v x z w) a!1))))
(check-sat)
