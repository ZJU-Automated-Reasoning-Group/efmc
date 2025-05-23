(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z1 (_ BitVec 64)) (z2 (_ BitVec 64)) (z3 (_ BitVec 64))) 
       (=> ( and ( bvsge x (_ bv0 64) ) ( bvsle x (_ bv10 64) ) ( bvsle y (_ bv10 64) ) ( bvsge y (_ bv0 64) ) ) (inv x y z1 z2 z3))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z1 (_ BitVec 64)) (z2 (_ BitVec 64)) (z3 (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (z1! (_ BitVec 64)) (z2! (_ BitVec 64)) (z3! (_ BitVec 64))) 
       (=> (and (inv x y z1 z2 z3) ( and ( = x! ( bvadd x (_ bv10 64) ) ) ( = y! ( bvadd y (_ bv10 64) ) ) )) (inv x! y! z1! z2! z3!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z1 (_ BitVec 64)) (z2 (_ BitVec 64)) (z3 (_ BitVec 64))) 
       (=> (inv x y z1 z2 z3) ( not ( and ( = x (_ bv20 64) ) ( = y (_ bv0 64) ) ) ))))
(check-sat)
