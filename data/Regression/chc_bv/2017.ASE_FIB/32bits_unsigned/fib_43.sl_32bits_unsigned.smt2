(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (t (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( and ( not ( = x y ) ) ( = i (_ bv0 32) ) ( = t y ) ) (inv i t x y))))
(assert (forall ((i (_ BitVec 32)) (t (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (i! (_ BitVec 32)) (t! (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv i t x y) ( or ( and ( bvugt x (_ bv0 32) ) ( = i! i ) ( = t! t ) ( = x! x ) ( = y! ( bvadd x y ) ) ) ( and ( bvule x (_ bv0 32) ) ( = i! i ) ( = t! t ) ( = x! x ) ( = y! y ) ) )) (inv i! t! x! y!))))
(assert (forall ((i (_ BitVec 32)) (t (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv i t x y) ( bvuge y t ))))
(check-sat)