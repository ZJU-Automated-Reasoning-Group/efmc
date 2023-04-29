(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (=> (and (= x #x0000000000000000) (= y #x0000000000000000)) (inv x y))))
(assert (forall ((x (_ BitVec 64))
         (y (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64)))
  (let ((a!1 (= y!
                (ite (bvsge x #x0000000000001d4c)
                     (ite (bvsge x #x00000000000030d4)
                          (bvsub y #x0000000000000002)
                          (bvadd y #x0000000000000001))
                     (ite (bvsge x #x00000000000009c4)
                          (bvadd y #x0000000000000001)
                          (bvsub y #x0000000000000002))))))
    (=> (and (inv x y) (= x! (bvadd x #x0000000000000001)) a!1) (inv x! y!)))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (let ((a!1 (not (and (= x #x0000000000003a98) (not (= y #x0000000000000000))))))
    (=> (inv x y) a!1))))
(check-sat)
