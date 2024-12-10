(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (n (_ BitVec 32)) (a (_ BitVec 32)) (b (_ BitVec 32))) 
       (=> ( and ( = i (_ bv0 32) ) ( = a (_ bv0 32) ) ( = b (_ bv0 32) ) ( bvuge n (_ bv0 32) ) ) (inv i n a b))))
(assert (forall ((i (_ BitVec 32)) (n (_ BitVec 32)) (a (_ BitVec 32)) (b (_ BitVec 32)) (i! (_ BitVec 32)) (n! (_ BitVec 32)) (a! (_ BitVec 32)) (b! (_ BitVec 32))) 
       (=> (and (inv i n a b) ( or ( and ( bvult i n ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = a! ( bvadd a (_ bv1 32) ) ) ( = b! ( bvadd b (_ bv2 32) ) ) ( = n! n ) ) ( and ( bvult i n ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = a! ( bvadd a (_ bv2 32) ) ) ( = b! ( bvadd b (_ bv1 32) ) ) ( = n! n ) ) ( and ( bvuge i n ) ( = i! i ) ( = a! a ) ( = b! b ) ( = n! n ) ) )) (inv i! n! a! b!))))
(assert (forall ((i (_ BitVec 32)) (n (_ BitVec 32)) (a (_ BitVec 32)) (b (_ BitVec 32))) 
       (=> (inv i n a b) ( => ( not ( bvult i n ) ) ( = ( bvadd a b ) ( bvadd n n n ) ) ))))
(check-sat)