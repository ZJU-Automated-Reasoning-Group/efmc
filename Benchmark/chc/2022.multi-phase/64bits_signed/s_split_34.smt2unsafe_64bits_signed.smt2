(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (=> (and (= x #x0000000000000000) (= y #x0000000000000001)) (inv x y))))
(assert (forall ((x (_ BitVec 64))
         (y (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64)))
  (let ((a!1 (and (bvsgt x!
                         (bvadd #x0000000000000001 (bvnot #x0000000000000064)))
                  (bvslt x! #x0000000000000064))))
  (let ((a!2 (= y! (ite a!1 y (bvadd #x0000000000000001 (bvnot y))))))
    (=> (and (inv x y) (= x! (bvadd x y)) a!2) (inv x! y!))))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (let ((a!1 (and (bvsge x
                         (bvadd #x0000000000000001 (bvnot #x0000000000000064)))
                  (bvsle x #x0000000000000064))))
    (=> (inv x y) (not a!1)))))
(check-sat)
