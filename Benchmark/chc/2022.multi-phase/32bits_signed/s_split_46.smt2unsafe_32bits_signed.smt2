(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) (=> (= x #x00000000) (inv x y))))
(assert (forall ((x (_ BitVec 32))
         (y (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32)))
  (let ((a!1 (= x!
                (ite (bvslt (bvsdiv x #x00000005) #x000000c8)
                     (bvadd x #x00000001)
                     (bvadd x #x00000005)))))
  (let ((a!2 (and (inv x y) a!1 (= y! (ite (= x #x000003e8) #x00000000 y)))))
    (=> a!2 (inv x! y!))))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (=> (inv x y) (not (and (bvsge x #x000007d0) (= y #x00000000))))))
(check-sat)
