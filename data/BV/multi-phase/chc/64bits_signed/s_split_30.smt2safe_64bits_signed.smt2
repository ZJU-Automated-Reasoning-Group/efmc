(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) Bool)
(assert (forall ((y (_ BitVec 64))
         (z (_ BitVec 64))
         (x (_ BitVec 64))
         (w (_ BitVec 64)))
  (let ((a!1 (and (= x #x0000000000000034)
                  (= y #x0000000000000061)
                  (= z (bvadd #x0000000000000001 (bvnot #x000000000000004c)))
                  (= w #x0000000000000000))))
    (=> a!1 (inv y z x w)))))
(assert (forall ((y (_ BitVec 64))
         (z (_ BitVec 64))
         (x (_ BitVec 64))
         (w (_ BitVec 64))
         (x! (_ BitVec 64))
         (y! (_ BitVec 64))
         (z! (_ BitVec 64))
         (w! (_ BitVec 64)))
  (let ((a!1 (bvadd (bvmul (bvadd #x0000000000000001 (bvnot #x0000000000000005))
                           x)
                    (bvmul #x0000000000000003 y)
                    (bvmul #x0000000000000004 z)
                    #x0000000000000001
                    (bvnot #x0000000000002232))))
  (let ((a!2 (and (inv y z x w)
                  (= x! (bvsub #x000000000000000d (bvmul #x0000000000000007 x)))
                  (= y! (bvsub #x0000000000000036 (bvmul #x0000000000000002 y)))
                  (= z! a!1)
                  (= w! (ite (bvsgt z! #x0000000000000000) (bvsub w x) w)))))
    (=> a!2 (inv x! y! z! w!))))))
(assert (forall ((y (_ BitVec 64))
         (z (_ BitVec 64))
         (x (_ BitVec 64))
         (w (_ BitVec 64)))
  (=> (inv y z x w)
      (not (and (bvsge y #x0000000000013c12) (bvsle w #x0000000000000000))))))
(check-sat)
