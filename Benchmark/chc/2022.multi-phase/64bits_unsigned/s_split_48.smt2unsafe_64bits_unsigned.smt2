(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (=> (and (= x #x0000000000000000) (= y #x0000000000000000)) (inv x y))))
(assert (forall ((x (_ BitVec 64))
         (y (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64)))
  (let ((a!1 (= y!
                (ite (bvult x #x0000000000001388)
                     (ite (bvuge x #x0000000000000fa0)
                          (bvadd y #x0000000000000004)
                          (bvadd y #x0000000000000001))
                     (ite (bvuge x #x0000000000001770)
                          (bvsub y #x0000000000000001)
                          (bvsub y #x0000000000000004))))))
    (=> (and (inv x y) (= x! (bvadd x #x0000000000000001)) a!1) (inv x! y!)))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (=> (inv x y) (not (and (= x #x0000000000002710) (= y #x0000000000000000))))))
(check-sat)
