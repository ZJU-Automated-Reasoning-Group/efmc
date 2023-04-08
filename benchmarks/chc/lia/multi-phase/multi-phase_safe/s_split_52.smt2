(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)
(assert (forall ((c0 Int) (y0 Int) (x0 Int))
  (=> (and (= x0 0) (= y0 c0) (= c0 5000)) (inv x0 y0 c0))))
(assert (forall ((c0 Int) (y1 Int) (x1 Int) (y0 Int) (x0 Int))
  (let ((a!1 (and (inv x0 y0 c0)
                  (= x1 (+ x0 1))
                  (= y1 (ite (>= x0 c0) (+ y0 1) (- y0 1))))))
    (=> a!1 (inv x1 y1 c0)))))
(assert (forall ((c0 Int) (y0 Int) (x0 Int))
  (=> (and (inv x0 y0 c0) (= x0 (* 2 c0)) (not (= y0 c0))) false)))
(check-sat)