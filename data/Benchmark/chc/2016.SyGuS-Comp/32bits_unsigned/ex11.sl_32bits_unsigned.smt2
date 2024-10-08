(set-logic HORN)
(declare-fun inv ((_ BitVec 32) ) Bool)
(assert (forall ((c (_ BitVec 32))) 
       (=> ( = c (_ bv0 32) ) (inv c))))
(assert (forall ((c (_ BitVec 32)) (c! (_ BitVec 32))) 
       (=> (and (inv c) ( or ( and ( not ( = c (_ bv4 32) ) ) ( = c! ( bvadd c (_ bv1 32) ) ) ) ( and ( = c (_ bv4 32) ) ( = c! (_ bv1 32) ) ) )) (inv c!))))
(assert (forall ((c (_ BitVec 32))) 
       (=> (inv c) ( not ( and ( not ( = c (_ bv4 32) ) ) ( or ( bvult c (_ bv0 32) ) ( bvugt c (_ bv4 32) ) ) ) ))))
(check-sat)
