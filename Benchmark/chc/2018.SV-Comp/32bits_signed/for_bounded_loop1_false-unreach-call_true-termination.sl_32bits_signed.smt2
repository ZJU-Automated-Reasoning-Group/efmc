(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> ( and ( = i (_ bv0 32) ) ( = x (_ bv0 32) ) ( = y (_ bv0 32) ) ( bvsgt n (_ bv0 32) ) ) (inv i x y n))))
(assert (forall ((i (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (n (_ BitVec 32)) (i! (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (n! (_ BitVec 32))) 
       (=> (and (inv i x y n) ( and ( bvslt i n ) ( = x! ( bvadd x y! ) ) ( not ( = y! (_ bv0 32) ) ) ( = i! i ) ( = n! n ) )) (inv i! x! y! n!))))
(assert (forall ((i (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> (inv i x y n) ( or ( bvslt i n ) ( = x (_ bv0 32) ) ))))
(check-sat)
