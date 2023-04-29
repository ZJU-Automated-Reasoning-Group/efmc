(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (sum (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> ( and ( = sum (_ bv0 32) ) ( bvuge n (_ bv0 32) ) ( = i (_ bv0 32) ) ) (inv i sum n))))
(assert (forall ((i (_ BitVec 32)) (sum (_ BitVec 32)) (n (_ BitVec 32)) (i! (_ BitVec 32)) (sum! (_ BitVec 32)) (n! (_ BitVec 32))) 
       (=> (and (inv i sum n) ( or ( and ( bvult i n ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = sum! ( bvadd sum i ) ) ( = n! n ) ) ( and ( bvuge i n ) ( = i! i ) ( = sum! sum ) ( = n! n ) ) )) (inv i! sum! n!))))
(assert (forall ((i (_ BitVec 32)) (sum (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> (inv i sum n) ( => ( bvuge i n ) ( bvuge sum (_ bv0 32) ) ))))
(check-sat)
