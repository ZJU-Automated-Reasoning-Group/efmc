(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (c (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> ( and ( = i (_ bv0 64) ) ( = c (_ bv0 64) ) ( bvsgt n (_ bv0 64) ) ) (inv i c n))))
(assert (forall ((i (_ BitVec 64)) (c (_ BitVec 64)) (n (_ BitVec 64)) (i! (_ BitVec 64)) (c! (_ BitVec 64)) (n! (_ BitVec 64))) 
       (=> (and (inv i c n) ( or ( and ( bvsge i n ) ( = i! i ) ( = c! c ) ( = n! n ) ) ( and ( bvslt i n ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = c! ( bvadd c i ) ) ( = n! n ) ) )) (inv i! c! n!))))
(assert (forall ((i (_ BitVec 64)) (c (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> (inv i c n) ( => ( bvsge i n ) ( bvsge c (_ bv0 64) ) ))))
(check-sat)
