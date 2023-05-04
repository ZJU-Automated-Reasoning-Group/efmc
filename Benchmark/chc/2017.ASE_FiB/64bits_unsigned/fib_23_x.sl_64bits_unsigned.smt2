(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (sum (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> ( and ( = sum (_ bv0 64) ) ( bvuge n (_ bv0 64) ) ( = i (_ bv0 64) ) ) (inv i sum n))))
(assert (forall ((i (_ BitVec 64)) (sum (_ BitVec 64)) (n (_ BitVec 64)) (i! (_ BitVec 64)) (sum! (_ BitVec 64)) (n! (_ BitVec 64))) 
       (=> (and (inv i sum n) ( or ( and ( bvult i n ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = sum! ( bvadd sum i ) ) ( = n! n ) ) ( and ( bvuge i n ) ( = i! i ) ( = sum! sum ) ( = n! n ) ) )) (inv i! sum! n!))))
(assert (forall ((i (_ BitVec 64)) (sum (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> (inv i sum n) ( => ( bvuge i n ) ( bvuge sum (_ bv0 64) ) ))))
(check-sat)