(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)
(assert (forall ((z0 Int) (y0 Int) (x0 Int))
  (=> (and (= x0 0) (= y0 0) (= z0 0)) (inv x0 y0 z0))))
(assert (forall ((z1 Int) (y1 Int) (x1 Int) (z0 Int) (y0 Int) (x0 Int))
  (let ((a!1 (= z1 (ite (= (div z0 100) (div x1 100)) z0 (+ z0 100)))))
  (let ((a!2 (and (inv x0 y0 z0) (= x1 (+ 1 x0)) (= y1 (mod (+ y0 1) 100)) a!1)))
    (=> a!2 (inv x1 y1 z1))))))
(assert (forall ((y0 Int) (z0 Int) (x0 Int))
  (let ((a!1 (and (inv x0 y0 z0) (not (= x0 (+ z0 y0))))))
    (=> a!1 false))))
(check-sat)