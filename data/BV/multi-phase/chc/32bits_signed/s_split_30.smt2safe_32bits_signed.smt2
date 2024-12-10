(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((y (_ BitVec 32))
         (z (_ BitVec 32))
         (x (_ BitVec 32))
         (w (_ BitVec 32)))
  (let ((a!1 (and (= x #x00000034)
                  (= y #x00000061)
                  (= z (bvadd #x00000001 (bvnot #x0000004c)))
                  (= w #x00000000))))
    (=> a!1 (inv y z x w)))))
(assert (forall ((y (_ BitVec 32))
         (z (_ BitVec 32))
         (x (_ BitVec 32))
         (w (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32))
         (z! (_ BitVec 32))
         (w! (_ BitVec 32)))
  (let ((a!1 (bvadd (bvmul (bvadd #x00000001 (bvnot #x00000005)) x)
                    (bvmul #x00000003 y)
                    (bvmul #x00000004 z)
                    #x00000001
                    (bvnot #x00002232))))
  (let ((a!2 (and (inv y z x w)
                  (= x! (bvsub #x0000000d (bvmul #x00000007 x)))
                  (= y! (bvsub #x00000036 (bvmul #x00000002 y)))
                  (= z! a!1)
                  (= w! (ite (bvsgt z! #x00000000) (bvsub w x) w)))))
    (=> a!2 (inv x! y! z! w!))))))
(assert (forall ((y (_ BitVec 32))
         (z (_ BitVec 32))
         (x (_ BitVec 32))
         (w (_ BitVec 32)))
  (=> (inv y z x w) (not (and (bvsge y #x00013c12) (bvsle w #x00000000))))))
(check-sat)