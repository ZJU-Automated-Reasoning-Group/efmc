(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (=> (and (= x #x00000000) (= y #x00001388)) (inv x y))))
(assert (forall ((x (_ BitVec 32))
         (y (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32)))
  (let ((a!1 (and (inv x y)
                  (= x! (bvadd x #x00000001))
                  (= y! (ite (bvsge x #x00001388) (bvadd y #x00000001) y)))))
    (=> a!1 (inv x! y!)))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (let ((a!1 (not (and (= x #x00002710) (not (= y x))))))
    (=> (inv x y) a!1))))
(check-sat)
