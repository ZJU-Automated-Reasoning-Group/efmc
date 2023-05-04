(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((y (_ BitVec 32)) (z (_ BitVec 32)) (c (_ BitVec 32))) 
       (=> ( and ( = c (_ bv0 32) ) ( bvuge y (_ bv0 32) ) ( bvuge (_ bv127 32) y ) ( = z ( bvmul (_ bv36 32) y ) ) ) (inv y z c))))
(assert (forall ((y (_ BitVec 32)) (z (_ BitVec 32)) (c (_ BitVec 32)) (y! (_ BitVec 32)) (z! (_ BitVec 32)) (c! (_ BitVec 32))) 
       (=> (and (inv y z c) ( and ( bvult c (_ bv36 32) ) ( = z! ( bvadd z (_ bv1 32) ) ) ( = c! ( bvadd c (_ bv1 32) ) ) ( = y! y ) )) (inv y! z! c!))))
(assert (forall ((y (_ BitVec 32)) (z (_ BitVec 32)) (c (_ BitVec 32))) 
       (=> (inv y z c) ( not ( and ( bvult c (_ bv36 32) ) ( or ( bvult z (_ bv0 32) ) ( bvuge z (_ bv4608 32) ) ) ) ))))
(check-sat)