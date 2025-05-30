(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (and (bvugt x #x0000000000000000)
           (bvult y #x0000000000000000)
           (= z #x0000000000000001))
      (inv x y z))))
(assert (forall ((x (_ BitVec 64))
         (y (_ BitVec 64))
         (z (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64))
         (z! (_ BitVec 64)))
  (let ((a!1 (and (inv x y z)
                  (= x! (bvadd x #x0000000000000001))
                  (= y! (bvadd y #x0000000000000002))
                  (= z!
                     (ite (bvuge y #x0000000000000000)
                          (bvmul z #x0000000000000002)
                          z)))))
    (=> a!1 (inv x! y! z!)))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (inv x y z) (not (and (bvuge y x) (bvule z #x0000000000000001))))))
(check-sat)
