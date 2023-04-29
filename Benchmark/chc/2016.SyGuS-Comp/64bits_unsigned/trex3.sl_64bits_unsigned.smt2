(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x1 (_ BitVec 64)) (x2 (_ BitVec 64)) (x3 (_ BitVec 64)) (d1 (_ BitVec 64)) (d2 (_ BitVec 64)) (d3 (_ BitVec 64))) 
       (=> ( and ( = d1 (_ bv1 64) ) ( = d2 (_ bv1 64) ) ( = d3 (_ bv1 64) ) ) (inv x1 x2 x3 d1 d2 d3))))
(assert (forall ((x1 (_ BitVec 64)) (x2 (_ BitVec 64)) (x3 (_ BitVec 64)) (d1 (_ BitVec 64)) (d2 (_ BitVec 64)) (d3 (_ BitVec 64)) (x1! (_ BitVec 64)) (x2! (_ BitVec 64)) (x3! (_ BitVec 64)) (d1! (_ BitVec 64)) (d2! (_ BitVec 64)) (d3! (_ BitVec 64))) 
       (=> (and (inv x1 x2 x3 d1 d2 d3) ( let ( ( a!1 ( and ( = d1! d1 ) ( = d2! d2 ) ( = d3! d3 ) ) ) ) ( let ( ( a!2 ( and ( = x2! x2 ) ( and ( = x3! x3 ) a!1 ) ( bvugt x1 (_ bv0 64) ) ( bvugt x2 (_ bv0 64) ) ( bvugt x3 (_ bv0 64) ) ( = x1! ( bvadd x1 ( bvsub (_ bv0 64) d1 ) ) ) ) ) ( a!3 ( and ( = x1! x1 ) ( and ( = x3! x3 ) a!1 ) ( bvugt x1 (_ bv0 64) ) ( bvugt x2 (_ bv0 64) ) ( bvugt x3 (_ bv0 64) ) ( = x2! ( bvadd x2 ( bvsub (_ bv0 64) d2 ) ) ) ) ) ( a!4 ( and ( = x1! x1 ) ( = x2! x2 ) a!1 ( bvugt x1 (_ bv0 64) ) ( bvugt x2 (_ bv0 64) ) ( bvugt x3 (_ bv0 64) ) ( = x3! ( bvadd x3 ( bvsub (_ bv0 64) d3 ) ) ) ) ) ) ( or a!2 a!3 a!4 ) ) )) (inv x1! x2! x3! d1! d2! d3!))))
(assert (forall ((x1 (_ BitVec 64)) (x2 (_ BitVec 64)) (x3 (_ BitVec 64)) (d1 (_ BitVec 64)) (d2 (_ BitVec 64)) (d3 (_ BitVec 64))) 
       (=> (inv x1 x2 x3 d1 d2 d3) ( or ( bvult x1 (_ bv0 64) ) ( bvult x2 (_ bv0 64) ) ( bvult x3 (_ bv0 64) ) ( = x1 (_ bv0 64) ) ( = x2 (_ bv0 64) ) ( = x3 (_ bv0 64) ) ))))
(check-sat)
