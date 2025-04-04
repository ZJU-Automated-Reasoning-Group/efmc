(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((c (_ BitVec 32)) (n (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> ( and ( = c (_ bv0 32) ) ( bvugt n (_ bv0 32) ) ) (inv c n v1 v2 v3))))
(assert (forall ((c (_ BitVec 32)) (n (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32)) (c! (_ BitVec 32)) (n! (_ BitVec 32)) (v1! (_ BitVec 32)) (v2! (_ BitVec 32)) (v3! (_ BitVec 32))) 
       (=> (and (inv c n v1 v2 v3) ( or ( and ( bvugt c n ) ( = c! ( bvadd c (_ bv1 32) ) ) ) ( and ( = c n ) ( = c! (_ bv1 32) ) ) )) (inv c! n! v1! v2! v3!))))
(assert (forall ((c (_ BitVec 32)) (n (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> (inv c n v1 v2 v3) ( let ( ( a!1 ( or ( and ( not ( = c n ) ) ( or ( bvult c (_ bv0 32) ) ( bvugt c n ) ) ) ( and ( = c n ) ( bvugt n ( bvadd (_ bv1 32) ( bvnot (_ bv1 32) ) ) ) ) ) ) ) ( not a!1 ) ))))
(check-sat)
