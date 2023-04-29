(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (=> (and (= x #x00000000) (= y #x00000001)) (inv x y))))
(assert (forall ((x (_ BitVec 32))
         (y (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32)))
  (let ((a!1 (and (bvugt x! (bvadd #x00000001 (bvnot #x00000064)))
                  (bvult x! #x00000064))))
  (let ((a!2 (= y! (ite a!1 y (bvadd #x00000001 (bvnot y))))))
    (=> (and (inv x y) (= x! (bvadd x y)) a!2) (inv x! y!))))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (let ((a!1 (and (bvuge x (bvadd #x00000001 (bvnot #x00000064)))
                  (bvule x #x00000064))))
    (=> (inv x y) (not a!1)))))
(check-sat)
