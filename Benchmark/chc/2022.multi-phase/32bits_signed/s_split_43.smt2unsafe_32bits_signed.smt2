(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (=> (and (= x #x00000000) (= y #x00000000)) (inv x y))))
(assert (forall ((x (_ BitVec 32))
         (y (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32)))
  (let ((a!1 (= y!
                (ite (bvsge x #x02faf080)
                     (ite (bvsge x #x05f5e100) y (bvadd y #x00000001))
                     #x00000000))))
    (=> (and (inv x y) (= x! (bvadd #x00000001 x)) a!1) (inv x! y!)))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (=> (inv x y) (not (and (bvsge x #x05f5e100) (= y #x02faf080))))))
(check-sat)
