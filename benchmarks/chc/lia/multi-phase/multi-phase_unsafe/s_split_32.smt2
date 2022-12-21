(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)
(assert (forall ((z0 Int) (w0 Int) (y0 Int) (x0 Int))
  (=> (and (= x0 z0) (= y0 0) (= w0 1) (or (= z0 0) (= z0 1)))
      (inv x0 y0 w0 z0))))
(assert (forall ((z1 Int)
         (w1 Int)
         (y1 Int)
         (x1 Int)
         (w0 Int)
         (y0 Int)
         (x0 Int)
         (z0 Int))
  (let ((a!1 (= w1 (ite (= z0 (mod x0 2)) (+ w0 y0) (- w0 1)))))
  (let ((a!2 (and (inv x0 y0 w0 z0)
                  (= x1 (+ 1 x0))
                  (= y1 (+ y0 x0 (- 3)))
                  (= z1 (- 1 z0))
                  a!1)))
    (=> a!2 (inv x1 y1 w1 z1))))))
(assert (forall ((w0 Int) (x0 Int) (z0 Int) (y0 Int))
  (=> (and (inv x0 y0 w0 z0) (> x0 10) (>= w0 0)) false)))
(check-sat)
