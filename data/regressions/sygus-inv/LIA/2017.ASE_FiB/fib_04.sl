(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int)))

(define-fun pre_fun ((x Int) (y Int)) Bool
    (= x (- 50)))
(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (or (and (< x 0) (= x! (+ x y)) (= y! (+ y 1))) (and (>= x 0) (= x! x) (= y! y))))
(define-fun post_fun ((x Int) (y Int)) Bool
    (=> (not (< x 0)) (>= y 0)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

;  (define-fun inv_fun ((x Int) (y Int)) Bool (or (not (>= x 0)) (>= y 0)))