(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x1 (_ BitVec 32)) (x2 (_ BitVec 32)) (x3 (_ BitVec 32))) 
       (=> ( and ( = x1 (_ bv0 32) ) ( = x2 (_ bv0 32) ) ( = x3 (_ bv0 32) ) ) (inv x1 x2 x3))))
(assert (forall ((x1 (_ BitVec 32)) (x2 (_ BitVec 32)) (x3 (_ BitVec 32)) (x1! (_ BitVec 32)) (x2! (_ BitVec 32)) (x3! (_ BitVec 32))) 
       (=> (and (inv x1 x2 x3) ( and ( bvsle x1! x2! ) ( or ( bvsge x2! (_ bv0 32) ) ( bvsle ( bvsub x2! x3! ) (_ bv2 32) ) ) )) (inv x1! x2! x3!))))
(assert (forall ((x1 (_ BitVec 32)) (x2 (_ BitVec 32)) (x3 (_ BitVec 32))) 
       (=> (inv x1 x2 x3) ( and ( bvsle x1 x2 ) ( or ( bvsge x2 (_ bv0 32) ) ( bvsle ( bvsub x2 x3 ) (_ bv2 32) ) ) ))))
(check-sat)