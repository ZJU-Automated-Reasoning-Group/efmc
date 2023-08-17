(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (and (= x #x0000000000000000)
           (bvsge y #x0000000000000064)
           (= z #x0000000000000000))
      (inv y x z))))
(assert (forall ((y (_ BitVec 64))
         (x (_ BitVec 64))
         (z (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64))
         (z! (_ BitVec 64)))
  (let ((a!1 (= z!
                (ite (bvsle y (bvsdiv x #x0000000000000032))
                     (bvadd z #x0000000000000001)
                     z))))
    (=> (and (inv y x z)
             (= x! (bvadd #x0000000000000001 x))
             (= y! (bvsub y #x0000000000000001))
             a!1)
        (inv x! y! z!)))))
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (let ((a!1 (not (and (= y #x0000000000000000)
                       (not (bvsle z #x0000000000000000))))))
    (=> (inv y x z) a!1))))
(check-sat)