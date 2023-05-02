(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z1 (_ BitVec 32)) (z2 (_ BitVec 32)) (z3 (_ BitVec 32))) 
       (=> ( and ( bvsge x (_ bv0 32) ) ( bvsle x (_ bv10 32) ) ( bvsle y (_ bv10 32) ) ( bvsge y (_ bv0 32) ) ) (inv x y z1 z2 z3))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z1 (_ BitVec 32)) (z2 (_ BitVec 32)) (z3 (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (z1! (_ BitVec 32)) (z2! (_ BitVec 32)) (z3! (_ BitVec 32))) 
       (=> (and (inv x y z1 z2 z3) ( and ( = x! ( bvadd x (_ bv10 32) ) ) ( = y! ( bvadd y (_ bv10 32) ) ) )) (inv x! y! z1! z2! z3!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z1 (_ BitVec 32)) (z2 (_ BitVec 32)) (z3 (_ BitVec 32))) 
       (=> (inv x y z1 z2 z3) ( not ( and ( = x (_ bv20 32) ) ( = y (_ bv0 32) ) ) ))))
(check-sat)
