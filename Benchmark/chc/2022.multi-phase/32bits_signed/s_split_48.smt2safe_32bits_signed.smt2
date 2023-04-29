(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (=> (and (= x #x00000000) (= y #x00000000)) (inv x y))))
(assert (forall ((x (_ BitVec 32))
         (y (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32)))
  (let ((a!1 (= y!
                (ite (bvslt x #x00001388)
                     (ite (bvsge x #x00000fa0)
                          (bvadd y #x00000004)
                          (bvadd y #x00000001))
                     (ite (bvsge x #x00001770)
                          (bvsub y #x00000001)
                          (bvsub y #x00000004))))))
    (=> (and (inv x y) (= x! (bvadd x #x00000001)) a!1) (inv x! y!)))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (let ((a!1 (not (and (= x #x00002710) (not (= y #x00000000))))))
    (=> (inv x y) a!1))))
(check-sat)
