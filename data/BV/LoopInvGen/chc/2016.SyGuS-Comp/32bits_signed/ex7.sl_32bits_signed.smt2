(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (i (_ BitVec 32))) 
       (=> ( and ( = i (_ bv0 32) ) ( bvsge x (_ bv0 32) ) ( bvsge y (_ bv0 32) ) ( bvsge x y ) ) (inv x y i))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (i (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (i! (_ BitVec 32))) 
       (=> (and (inv x y i) ( and ( bvslt i y ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = y! y ) ( = x! x ) )) (inv x! y! i!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (i (_ BitVec 32))) 
       (=> (inv x y i) ( not ( and ( bvslt i y ) ( or ( bvsge i x ) ( bvsgt (_ bv0 32) i ) ) ) ))))
(check-sat)