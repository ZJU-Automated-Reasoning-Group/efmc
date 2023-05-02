(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((y (_ BitVec 32)) (x (_ BitVec 32)) (z (_ BitVec 32)))
  (=> (= x #x00000000) (inv y x z))))
(assert (forall ((y (_ BitVec 32))
         (x (_ BitVec 32))
         (z (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32))
         (z! (_ BitVec 32)))
  (let ((a!1 (= y!
                (ite (bvuge x #x000bae70)
                     (ite (bvuge x #x000d3510) y (bvadd y #x00000001))
                     #x00000000)))
        (a!2 (= z!
                (ite (bvuge x #x000a1eda)
                     (ite (bvuge x #x000ba57a) z (bvadd z #x00000001))
                     #x00000000))))
    (=> (and (inv y x z) (= x! (bvadd #x00000001 x)) a!1 a!2) (inv x! y! z!)))))
(assert (forall ((y (_ BitVec 32)) (x (_ BitVec 32)) (z (_ BitVec 32)))
  (let ((a!1 (not (and (bvuge x #x000ebbb0) (not (= y z))))))
    (=> (inv y x z) a!1))))
(check-sat)
