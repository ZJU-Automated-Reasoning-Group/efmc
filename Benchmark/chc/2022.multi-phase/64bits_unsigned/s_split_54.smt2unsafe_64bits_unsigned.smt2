(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (and (= x #x0000000000000000)
           (= y #x0000000000001f40)
           (= z #x0000000000000000))
      (inv y x z))))
(assert (forall ((y (_ BitVec 64))
         (x (_ BitVec 64))
         (z (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64))
         (z! (_ BitVec 64)))
  (let ((a!1 (and (inv y x z)
                  (= x! (bvadd x #x0000000000000001))
                  (= y!
                     (ite (bvuge x #x0000000000001f40)
                          (bvadd y #x0000000000000001)
                          (bvsub y #x0000000000000001)))
                  (= z!
                     (ite (bvult x #x0000000000001f40)
                          (bvadd z #x0000000000000001)
                          (bvsub z #x0000000000000001))))))
    (=> a!1 (inv x! y! z!)))))
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (inv y x z)
      (not (and (= x #x0000000000003e80)
                (= y #x0000000000001f40)
                (= z #x0000000000000000))))))
(check-sat)
