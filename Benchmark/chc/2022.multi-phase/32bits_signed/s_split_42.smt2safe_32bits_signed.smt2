(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)))
  (=> (and (= x #x00000000) (= y z) (= z #x00000000)) (inv x y z))))
(assert (forall ((x (_ BitVec 32))
         (y (_ BitVec 32))
         (z (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32))
         (z! (_ BitVec 32)))
  (let ((a!1 (and (inv x y z)
                  (= x! (bvadd x #x00000001))
                  (= y!
                     (ite (bvsge x #x000006e5)
                          (bvadd y #x00000002)
                          (bvadd y #x00000001)))
                  (= z!
                     (ite (bvsge y #x00001685)
                          (bvadd z #x00000003)
                          (bvadd z #x00000002))))))
    (=> a!1 (inv x! y! z!)))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)))
  (let ((a!1 (not (and (not (bvsle x #x000044f2)) (bvsle z #x00006c02)))))
    (=> (inv x y z) a!1))))
(check-sat)
