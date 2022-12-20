(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((i (_ BitVec 8)) (c (_ BitVec 8)) (n (_ BitVec 8))) 
       (=> ( and ( = i (_ bv0 8) ) ( = c (_ bv0 8) ) ( bvsgt n (_ bv0 8) ) ) (inv i c n))))
(assert (forall ((i (_ BitVec 8)) (c (_ BitVec 8)) (n (_ BitVec 8)) (i! (_ BitVec 8)) (c! (_ BitVec 8)) (n! (_ BitVec 8))) 
       (=> (and (inv i c n) ( or ( and ( bvsge i n ) ( = i! i ) ( = c! c ) ( = n! n ) ) ( and ( bvslt i n ) ( = i! ( bvadd i (_ bv1 8) ) ) ( = c! ( bvadd c i ) ) ( = n! n ) ) )) (inv i! c! n!))))
(assert (forall ((i (_ BitVec 8)) (c (_ BitVec 8)) (n (_ BitVec 8))) 
       (=> (inv i c n) ( => ( bvsge i n ) ( bvsge c (_ bv0 8) ) ))))
(check-sat)
