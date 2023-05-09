(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (and (= x #x0000000000000000)
           (bvuge y #x0000000000000064)
           (= z #x0000000000000000))
      (inv y x z))))
(assert (forall ((y (_ BitVec 64))
         (x (_ BitVec 64))
         (z (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64))
         (z! (_ BitVec 64)))
  (let ((a!1 (= z!
                (ite (bvule y (bvudiv x #x0000000000000032))
                     (bvadd z #x0000000000000001)
                     z))))
    (=> (and (inv y x z)
             (= x! (bvadd #x0000000000000001 x))
             (= y! (bvsub y #x0000000000000001))
             a!1)
        (inv x! y! z!)))))
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (inv y x z)
      (not (and (= y #x0000000000000000) (bvule z #x0000000000000000))))))
(check-sat)
