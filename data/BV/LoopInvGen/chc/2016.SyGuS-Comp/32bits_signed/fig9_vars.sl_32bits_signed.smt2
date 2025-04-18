(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z1 (_ BitVec 32)) (z2 (_ BitVec 32)) (z3 (_ BitVec 32))) 
       (=> ( and ( = x (_ bv0 32) ) ( = y (_ bv0 32) ) ) (inv x y z1 z2 z3))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z1 (_ BitVec 32)) (z2 (_ BitVec 32)) (z3 (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (z1! (_ BitVec 32)) (z2! (_ BitVec 32)) (z3! (_ BitVec 32))) 
       (=> (and (inv x y z1 z2 z3) ( and ( = x! x ) ( bvsle (_ bv0 32) y ) ( = y! ( bvadd x y ) ) )) (inv x! y! z1! z2! z3!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z1 (_ BitVec 32)) (z2 (_ BitVec 32)) (z3 (_ BitVec 32))) 
       (=> (inv x y z1 z2 z3) ( bvsge y (_ bv0 32) ))))
(check-sat)
