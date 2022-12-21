(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((y0 Int) (x0 Int)) (=> (and (= x0 1) (= y0 1)) (inv x0 y0))))
(assert (forall ((y1 Int) (x1 Int) (x0 Int) (y0 Int))
  (let ((a!1 (and (inv x0 y0)
                  (= x1 (* x0 2))
                  (= y1 (ite (< y0 16) (* y0 2) (mod x0 16))))))
    (=> a!1 (inv x1 y1)))))
(assert (forall ((y0 Int) (x0 Int))
  (=> (and (inv x0 y0) (> x0 16) (not (= 0 y0))) false)))
(check-sat)
