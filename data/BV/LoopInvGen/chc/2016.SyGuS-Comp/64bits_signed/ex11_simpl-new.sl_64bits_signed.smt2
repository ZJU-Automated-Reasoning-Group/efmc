(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((c (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> ( and ( = c (_ bv0 64) ) ( bvsgt n (_ bv0 64) ) ) (inv c n))))
(assert (forall ((c (_ BitVec 64)) (n (_ BitVec 64)) (c! (_ BitVec 64)) (n! (_ BitVec 64))) 
       (=> (and (inv c n) ( or ( and ( bvsgt c n ) ( = c! ( bvadd c (_ bv1 64) ) ) ( = n! n ) ) ( and ( = c n ) ( = c! (_ bv1 64) ) ( = n! n ) ) )) (inv c! n!))))
(assert (forall ((c (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> (inv c n) ( and ( or ( = c n ) ( and ( bvsge c (_ bv0 64) ) ( bvsle c n ) ) ) ( or ( not ( = c n ) ) ( bvsgt n ( bvadd (_ bv1 64) ( bvnot (_ bv1 64) ) ) ) ) ))))
(check-sat)
