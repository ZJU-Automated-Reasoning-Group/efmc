(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (let ((a!1 (and (= x (bvadd #x00000001 (bvnot #x00002710))) (= y #x00000000))))
    (=> a!1 (inv x y)))))
(assert (forall ((x (_ BitVec 32))
         (y (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32)))
  (let ((a!1 (= y!
                (ite (bvuge y x)
                     (bvadd #x00000001 (bvnot x))
                     (bvadd y #x00000002)))))
  (let ((a!2 (and (inv x y) (= x! (ite (bvuge y x) (bvadd x #x00000001) x)) a!1)))
    (=> a!2 (inv x! y!))))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (let ((a!1 (not (bvuge x (bvadd #x00000001 (bvnot #x00000001) y)))))
    (=> (inv x y) (not (and (bvuge x #x00000000) a!1))))))
(check-sat)
