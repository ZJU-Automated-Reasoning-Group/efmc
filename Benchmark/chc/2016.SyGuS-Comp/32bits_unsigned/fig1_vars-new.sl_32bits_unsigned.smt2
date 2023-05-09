(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z1 (_ BitVec 32)) (z2 (_ BitVec 32)) (z3 (_ BitVec 32))) 
       (=> ( = x ( bvadd (_ bv1 32) ( bvnot (_ bv15000 32) ) ) ) (inv x y z1 z2 z3))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z1 (_ BitVec 32)) (z2 (_ BitVec 32)) (z3 (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (z1! (_ BitVec 32)) (z2! (_ BitVec 32)) (z3! (_ BitVec 32))) 
       (=> (and (inv x y z1 z2 z3) ( and ( bvult x (_ bv0 32) ) ( = x! ( bvadd x y ) ) ( = y! ( bvadd y (_ bv1 32) ) ) )) (inv x! y! z1! z2! z3!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z1 (_ BitVec 32)) (z2 (_ BitVec 32)) (z3 (_ BitVec 32))) 
       (=> (inv x y z1 z2 z3) ( not ( and ( bvuge x (_ bv0 32) ) ( bvule y (_ bv0 32) ) ) ))))
(check-sat)
