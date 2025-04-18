(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((z (_ BitVec 64))
         (y (_ BitVec 64))
         (x (_ BitVec 64))
         (w (_ BitVec 64)))
  (=> (and (= x #x0000000000000000)
           (= y #x0000000000000000)
           (= z #x0000000000000000)
           (= w #x0000000000000000))
      (inv z y x w))))
(assert (forall ((z (_ BitVec 64))
         (y (_ BitVec 64))
         (x (_ BitVec 64))
         (w (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64))
         (z! (_ BitVec 64))
         (w! (_ BitVec 64)))
  (let ((a!1 (ite (bvsgt (bvsub y (bvmul #x000000000000000a x))
                         #x0000000000000000)
                  (bvadd z #x0000000000000001)
                  z))
        (a!2 (ite (bvsgt (bvsub y (bvmul #x000000000000000a x))
                         #x0000000000000000)
                  w
                  (bvadd w #x0000000000000001))))
    (=> (and (inv z y x w)
             (= x! (bvadd x #x0000000000000001))
             (= y! (bvadd y x))
             (= z! a!1)
             (= w! a!2))
        (inv x! y! z! w!)))))
(assert (forall ((z (_ BitVec 64))
         (y (_ BitVec 64))
         (x (_ BitVec 64))
         (w (_ BitVec 64)))
  (let ((a!1 (not (and (not (bvsle x #x0000000000000064)) (not (bvsle z w))))))
    (=> (inv z y x w) a!1))))
(check-sat)
