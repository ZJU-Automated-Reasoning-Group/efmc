(set-logic HORN)

; Declare floating-point variables
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun x! () (_ FloatingPoint 8 24))

; Declare the invariant function
(declare-fun inv ((_ FloatingPoint 8 24)) Bool)

; Initial condition: x is in [0.0, 10.0]
(define-fun init () Bool
  (and (fp.geq x ((_ to_fp 8 24) RNE 0.0))
       (fp.leq x ((_ to_fp 8 24) RNE 10.0))))

; Transition: x' = x + 1.0 (if x < 5.0)
(define-fun trans () Bool
  (ite (fp.lt x ((_ to_fp 8 24) RNE 5.0))
       (fp.eq x! (fp.add RNE x ((_ to_fp 8 24) RNE 1.0)))
       (fp.eq x! x)))

; Post condition: x should remain in [0.0, 10.0]
(define-fun post () Bool
  (and (fp.geq x ((_ to_fp 8 24) RNE 0.0))
       (fp.leq x ((_ to_fp 8 24) RNE 10.0))))

; CHC constraints
(assert (forall ((x (_ FloatingPoint 8 24)))
  (=> init (inv x))))

(assert (forall ((x (_ FloatingPoint 8 24)) (x! (_ FloatingPoint 8 24)))
  (=> (and (inv x) trans) (inv x!))))

(assert (forall ((x (_ FloatingPoint 8 24)))
  (=> (inv x) post)))

(check-sat) 