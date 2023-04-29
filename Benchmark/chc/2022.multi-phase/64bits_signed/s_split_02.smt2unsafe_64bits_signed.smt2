(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (and (= x #x0000000000000000)
           (= y #x00000000000000c8)
           (= z #x0000000000000190))
      (inv y x z))))
(assert (forall ((y (_ BitVec 64))
         (x (_ BitVec 64))
         (z (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64))
         (z! (_ BitVec 64)))
  (let ((a!1 (and (inv y x z)
                  (= x! (bvadd #x0000000000000001 x))
                  (= y!
                     (ite (bvslt x #x00000000000000c8)
                          (bvadd y #x0000000000000001)
                          y))
                  (= z!
                     (ite (bvslt x #x00000000000000c8)
                          z
                          (bvadd z #x0000000000000002))))))
    (=> a!1 (inv x! y! z!)))))
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (let ((a!1 (not (and (bvsge y #x0000000000000190)
                       (= z (bvmul #x0000000000000002 x))))))
    (=> (inv y x z) a!1))))
(check-sat)
