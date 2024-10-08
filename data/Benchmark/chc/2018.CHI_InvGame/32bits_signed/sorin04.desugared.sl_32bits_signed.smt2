(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((i (_ BitVec 32)) (a (_ BitVec 32)) (c (_ BitVec 32))) 
       (=> ( and ( = i (_ bv0 32) ) ( = a (_ bv0 32) ) ( = c (_ bv0 32) ) ) (inv i a c))))
(assert (forall ((i (_ BitVec 32)) (a (_ BitVec 32)) (c (_ BitVec 32)) (i! (_ BitVec 32)) (a! (_ BitVec 32)) (c! (_ BitVec 32))) 
       (=> (and (inv i a c) ( and ( bvslt i (_ bv10 32) ) ( = c! ( bvadd c (_ bv1 32) ( bvmul (_ bv6 32) a ) ) ) ( = a! ( bvadd a ( bvadd i (_ bv1 32) ) ) ) ( = i! ( bvadd i (_ bv1 32) ) ) )) (inv i! a! c!))))
(assert (forall ((i (_ BitVec 32)) (a (_ BitVec 32)) (c (_ BitVec 32))) 
       (=> (inv i a c) ( or ( bvslt i (_ bv10 32) ) ( = c ( bvmul i i i ) ) ))))
(check-sat)
