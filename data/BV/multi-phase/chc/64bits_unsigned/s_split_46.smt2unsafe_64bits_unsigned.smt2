(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (=> (= x #x0000000000000000) (inv x y))))
(assert (forall ((x (_ BitVec 64))
         (y (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64)))
  (let ((a!1 (= x!
                (ite (bvult (bvudiv x #x0000000000000005) #x00000000000000c8)
                     (bvadd x #x0000000000000001)
                     (bvadd x #x0000000000000005)))))
  (let ((a!2 (and (inv x y)
                  a!1
                  (= y! (ite (= x #x00000000000003e8) #x0000000000000000 y)))))
    (=> a!2 (inv x! y!))))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
  (=> (inv x y)
      (not (and (bvuge x #x00000000000007d0) (= y #x0000000000000000))))))
(check-sat)
