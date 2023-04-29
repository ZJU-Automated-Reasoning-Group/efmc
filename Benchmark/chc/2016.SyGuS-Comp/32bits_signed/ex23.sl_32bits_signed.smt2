(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((y (_ BitVec 32)) (z (_ BitVec 32)) (c (_ BitVec 32))) 
       (=> ( and ( = c (_ bv0 32) ) ( bvsge y (_ bv0 32) ) ( bvsge (_ bv127 32) y ) ( = z ( bvmul (_ bv36 32) y ) ) ) (inv y z c))))
(assert (forall ((y (_ BitVec 32)) (z (_ BitVec 32)) (c (_ BitVec 32)) (y! (_ BitVec 32)) (z! (_ BitVec 32)) (c! (_ BitVec 32))) 
       (=> (and (inv y z c) ( and ( bvslt c (_ bv36 32) ) ( = z! ( bvadd z (_ bv1 32) ) ) ( = c! ( bvadd c (_ bv1 32) ) ) ( = y! y ) )) (inv y! z! c!))))
(assert (forall ((y (_ BitVec 32)) (z (_ BitVec 32)) (c (_ BitVec 32))) 
       (=> (inv y z c) ( not ( and ( bvslt c (_ bv36 32) ) ( or ( bvslt z (_ bv0 32) ) ( bvsge z (_ bv4608 32) ) ) ) ))))
(check-sat)
