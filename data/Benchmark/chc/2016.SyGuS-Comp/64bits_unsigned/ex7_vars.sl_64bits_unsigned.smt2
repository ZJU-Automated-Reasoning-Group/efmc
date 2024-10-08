(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (i (_ BitVec 64)) (z1 (_ BitVec 64)) (z2 (_ BitVec 64)) (z3 (_ BitVec 64))) 
       (=> ( and ( = i (_ bv0 64) ) ( bvuge x (_ bv0 64) ) ( bvuge y (_ bv0 64) ) ( bvuge x y ) ) (inv x y i z1 z2 z3))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (i (_ BitVec 64)) (z1 (_ BitVec 64)) (z2 (_ BitVec 64)) (z3 (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (i! (_ BitVec 64)) (z1! (_ BitVec 64)) (z2! (_ BitVec 64)) (z3! (_ BitVec 64))) 
       (=> (and (inv x y i z1 z2 z3) ( and ( bvult i y ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = y! y ) ( = x! x ) )) (inv x! y! i! z1! z2! z3!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (i (_ BitVec 64)) (z1 (_ BitVec 64)) (z2 (_ BitVec 64)) (z3 (_ BitVec 64))) 
       (=> (inv x y i z1 z2 z3) ( not ( and ( bvult i y ) ( or ( bvuge i x ) ( bvugt (_ bv0 64) i ) ) ) ))))
(check-sat)
