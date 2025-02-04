(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (=> (and (= x #x0000000000000000) (= y #x0000000000001388)) (inv x y))))
(assert (forall ((x (_ BitVec 64))
         (y (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64)))
  (let ((a!1 (and (inv x y)
                  (= x! (bvadd x #x0000000000000001))
                  (= y!
                     (ite (bvsge x #x0000000000001388)
                          (bvadd y #x0000000000000001)
                          y)))))
    (=> a!1 (inv x! y!)))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (=> (inv x y) (not (and (= x #x0000000000002710) (= y x))))))
(check-sat)
