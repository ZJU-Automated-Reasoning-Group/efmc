(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)))
  (=> (and (bvugt x #x00000000) (bvult y #x00000000) (= z #x00000001))
      (inv x y z))))
(assert (forall ((x (_ BitVec 32))
         (y (_ BitVec 32))
         (z (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32))
         (z! (_ BitVec 32)))
  (let ((a!1 (and (inv x y z)
                  (= x! (bvadd x #x00000001))
                  (= y! (bvadd y #x00000002))
                  (= z! (ite (bvuge y #x00000000) (bvmul z #x00000002) z)))))
    (=> a!1 (inv x! y! z!)))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)))
  (=> (inv x y z) (not (and (bvuge y x) (bvule z #x00000001))))))
(check-sat)
