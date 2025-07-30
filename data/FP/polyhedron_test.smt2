(set-logic HORN)

; Declare floating-point variables
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun x! () (_ FloatingPoint 8 24))
(declare-fun y! () (_ FloatingPoint 8 24))

; Declare the invariant function
(declare-fun inv ((_ FloatingPoint 8 24) (_ FloatingPoint 8 24)) Bool)

; Initial condition: x >= 0.0 and y >= 0.0
(define-fun init () Bool
  (and (fp.geq x ((_ to_fp 8 24) RNE 0.0))
       (fp.geq y ((_ to_fp 8 24) RNE 0.0))))

; Transition: x' = x + 0.5, y' = y + 0.3 (if x + y < 10.0)
(define-fun trans () Bool
  (ite (fp.lt (fp.add RNE x y) ((_ to_fp 8 24) RNE 10.0))
       (and (fp.eq x! (fp.add RNE x ((_ to_fp 8 24) RNE 0.5)))
            (fp.eq y! (fp.add RNE y ((_ to_fp 8 24) RNE 0.3))))
       (and (fp.eq x! x) (fp.eq y! y))))

; Post condition: x + y <= 10.0
(define-fun post () Bool
  (fp.leq (fp.add RNE x y) ((_ to_fp 8 24) RNE 10.0)))

; CHC constraints
(assert (forall ((x (_ FloatingPoint 8 24)) (y (_ FloatingPoint 8 24)))
  (=> init (inv x y))))

(assert (forall ((x (_ FloatingPoint 8 24)) (y (_ FloatingPoint 8 24))
                (x! (_ FloatingPoint 8 24)) (y! (_ FloatingPoint 8 24)))
  (=> (and (inv x y) trans) (inv x! y!))))

(assert (forall ((x (_ FloatingPoint 8 24)) (y (_ FloatingPoint 8 24)))
  (=> (inv x y) post)))

(check-sat) 