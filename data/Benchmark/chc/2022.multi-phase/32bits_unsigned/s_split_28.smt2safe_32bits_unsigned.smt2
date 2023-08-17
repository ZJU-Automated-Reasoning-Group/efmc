(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((y (_ BitVec 32)) (x (_ BitVec 32)) (z (_ BitVec 32)))
  (=> (and (= x #x00000000) (bvuge y #x00000064) (= z #x00000000)) (inv y x z))))
(assert (forall ((y (_ BitVec 32))
         (x (_ BitVec 32))
         (z (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32))
         (z! (_ BitVec 32)))
  (let ((a!1 (= z! (ite (bvule y (bvudiv x #x00000032)) (bvadd z #x00000001) z))))
    (=> (and (inv y x z)
             (= x! (bvadd #x00000001 x))
             (= y! (bvsub y #x00000001))
             a!1)
        (inv x! y! z!)))))
(assert (forall ((y (_ BitVec 32)) (x (_ BitVec 32)) (z (_ BitVec 32)))
  (=> (inv y x z) (not (and (= y #x00000000) (bvule z #x00000000))))))
(check-sat)