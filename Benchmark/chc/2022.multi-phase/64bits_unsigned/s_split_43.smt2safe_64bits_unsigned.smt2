(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (=> (and (= x #x0000000000000000) (= y #x0000000000000000)) (inv x y))))
(assert (forall ((x (_ BitVec 64))
         (y (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64)))
  (let ((a!1 (= y!
                (ite (bvuge x #x0000000002faf080)
                     (ite (bvuge x #x0000000005f5e100)
                          y
                          (bvadd y #x0000000000000001))
                     #x0000000000000000))))
    (=> (and (inv x y) (= x! (bvadd #x0000000000000001 x)) a!1) (inv x! y!)))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (let ((a!1 (not (and (bvuge x #x0000000005f5e100)
                       (not (= y #x0000000002faf080))))))
    (=> (inv x y) a!1))))
(check-sat)