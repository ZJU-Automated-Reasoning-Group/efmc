(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((y (_ BitVec 32))
         (x (_ BitVec 32))
         (z (_ BitVec 32))
         (w (_ BitVec 32)))
  (=> (and (= x #x00000000) (bvsgt y z) (= w #x00000000)) (inv y x z w))))
(assert (forall ((y (_ BitVec 32))
         (x (_ BitVec 32))
         (z (_ BitVec 32))
         (w (_ BitVec 32))
         (x! (_ BitVec 32))
         (y! (_ BitVec 32))
         (z! (_ BitVec 32))
         (w! (_ BitVec 32)))
  (let ((a!1 (and (inv y x z w)
                  (= x! (bvadd #x00000005 x))
                  (= y! (bvadd #x00000003 y))
                  (= z! (bvadd #x00000001 z))
                  (= w!
                     (ite (bvslt x z) (bvadd w #x00000001) (bvsub w #x00000001))))))
    (=> a!1 (inv x! y! z! w!)))))
(assert (forall ((y (_ BitVec 32))
         (x (_ BitVec 32))
         (z (_ BitVec 32))
         (w (_ BitVec 32)))
  (let ((a!1 (not (and (not (bvsle x y)) (bvsle w #x00000000)))))
    (=> (inv y x z w) a!1))))
(check-sat)
