(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (and (= x #x0000000000000001)
           (= y #x0000000000000000)
           (= z #x0000000000000000))
      (inv y x z))))
(assert (forall ((y (_ BitVec 64))
         (x (_ BitVec 64))
         (z (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64))
         (z! (_ BitVec 64)))
  (let ((a!1 (and (inv y x z)
                  (= x! (bvadd #x0000000000000001 (bvnot x)))
                  (= y!
                     (ite (bvsgt x #x0000000000000000)
                          (bvadd y #x0000000000000001)
                          y))
                  (= z!
                     (ite (bvsgt x #x0000000000000000)
                          z
                          (bvadd z #x0000000000000001))))))
    (=> a!1 (inv x! y! z!)))))
(assert (forall ((y (_ BitVec 64)) (x (_ BitVec 64)) (z (_ BitVec 64)))
  (=> (inv y x z)
      (not (and (= x #x0000000000000001)
                (= y #x000000001467b6dd)
                (= #x000000001467b6dd z))))))
(check-sat)
