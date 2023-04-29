(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (= x #x0000000000000000) (inv y x z))))
(assert (forall ((y (_ BitVec 64))
         (x (_ BitVec 64))
         (z (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64))
         (z! (_ BitVec 64)))
  (let ((a!1 (= y!
                (ite (bvsge x #x00000000000bae70)
                     (ite (bvsge x #x00000000000d3510)
                          y
                          (bvadd y #x0000000000000001))
                     #x0000000000000000)))
        (a!2 (= z!
                (ite (bvsge x #x00000000000a1eda)
                     (ite (bvsge x #x00000000000ba57a)
                          z
                          (bvadd z #x0000000000000001))
                     #x0000000000000000))))
    (=> (and (inv y x z) (= x! (bvadd #x0000000000000001 x)) a!1 a!2)
        (inv x! y! z!)))))
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (inv y x z) (not (and (bvsge x #x00000000000ebbb0) (= y z))))))
(check-sat)
