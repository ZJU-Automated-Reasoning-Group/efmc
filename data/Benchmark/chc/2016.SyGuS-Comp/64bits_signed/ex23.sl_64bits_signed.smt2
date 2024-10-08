(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((y (_ BitVec 64)) (z (_ BitVec 64)) (c (_ BitVec 64))) 
       (=> ( and ( = c (_ bv0 64) ) ( bvsge y (_ bv0 64) ) ( bvsge (_ bv127 64) y ) ( = z ( bvmul (_ bv36 64) y ) ) ) (inv y z c))))
(assert (forall ((y (_ BitVec 64)) (z (_ BitVec 64)) (c (_ BitVec 64)) (y! (_ BitVec 64)) (z! (_ BitVec 64)) (c! (_ BitVec 64))) 
       (=> (and (inv y z c) ( and ( bvslt c (_ bv36 64) ) ( = z! ( bvadd z (_ bv1 64) ) ) ( = c! ( bvadd c (_ bv1 64) ) ) ( = y! y ) )) (inv y! z! c!))))
(assert (forall ((y (_ BitVec 64)) (z (_ BitVec 64)) (c (_ BitVec 64))) 
       (=> (inv y z c) ( not ( and ( bvslt c (_ bv36 64) ) ( or ( bvslt z (_ bv0 64) ) ( bvsge z (_ bv4608 64) ) ) ) ))))
(check-sat)
