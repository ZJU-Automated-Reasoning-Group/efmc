(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((c (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> ( and ( = c (_ bv0 32) ) ( bvsgt n (_ bv0 32) ) ) (inv c n))))
(assert (forall ((c (_ BitVec 32)) (n (_ BitVec 32)) (c! (_ BitVec 32)) (n! (_ BitVec 32))) 
       (=> (and (inv c n) ( or ( and ( not ( = c n ) ) ( = c! ( bvadd c (_ bv1 32) ) ) ( = n! n ) ) ( and ( = c n ) ( = c! (_ bv1 32) ) ( = n! n ) ) )) (inv c! n!))))
(assert (forall ((c (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> (inv c n) ( and ( or ( = c n ) ( and ( bvsge c (_ bv0 32) ) ( bvsle c n ) ) ) ( or ( not ( = c n ) ) ( bvsgt n ( bvadd (_ bv1 32) ( bvnot (_ bv1 32) ) ) ) ) ))))
(check-sat)