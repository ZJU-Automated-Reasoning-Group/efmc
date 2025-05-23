(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32)) (z (_ BitVec 32)))
  (=> (and (= x #x000003e8) (= z #x00000064)) (inv x z))))
(assert (forall ((x (_ BitVec 32))
         (z (_ BitVec 32))
         (x! (_ BitVec 32))
         (z! (_ BitVec 32)))
  (let ((a!1 (= x!
                (ite (bvslt (bvsdiv x #x0000000a) z)
                     (bvadd x #x00000001)
                     (bvsub x #x00000001))))
        (a!2 (= z!
                (ite (bvslt (bvsdiv x #x0000000a) z)
                     (bvsub z #x00000001)
                     (bvadd z #x00000001)))))
    (=> (and (inv x z) a!1 a!2) (inv x! z!)))))
(assert (forall ((x (_ BitVec 32)) (z (_ BitVec 32))) (=> (inv x z) (not (bvsle x z)))))
(check-sat)
