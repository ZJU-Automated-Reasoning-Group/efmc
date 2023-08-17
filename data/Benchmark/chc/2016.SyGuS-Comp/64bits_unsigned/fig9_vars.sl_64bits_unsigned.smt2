(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z1 (_ BitVec 64)) (z2 (_ BitVec 64)) (z3 (_ BitVec 64))) 
       (=> ( and ( = x (_ bv0 64) ) ( = y (_ bv0 64) ) ) (inv x y z1 z2 z3))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z1 (_ BitVec 64)) (z2 (_ BitVec 64)) (z3 (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (z1! (_ BitVec 64)) (z2! (_ BitVec 64)) (z3! (_ BitVec 64))) 
       (=> (and (inv x y z1 z2 z3) ( and ( = x! x ) ( bvule (_ bv0 64) y ) ( = y! ( bvadd x y ) ) )) (inv x! y! z1! z2! z3!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z1 (_ BitVec 64)) (z2 (_ BitVec 64)) (z3 (_ BitVec 64))) 
       (=> (inv x y z1 z2 z3) ( bvuge y (_ bv0 64) ))))
(check-sat)