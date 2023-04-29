(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((c (_ BitVec 64)) (n (_ BitVec 64)) (v1 (_ BitVec 64)) (v2 (_ BitVec 64)) (v3 (_ BitVec 64))) 
       (=> ( and ( = c (_ bv0 64) ) ( bvugt n (_ bv0 64) ) ) (inv c n v1 v2 v3))))
(assert (forall ((c (_ BitVec 64)) (n (_ BitVec 64)) (v1 (_ BitVec 64)) (v2 (_ BitVec 64)) (v3 (_ BitVec 64)) (c! (_ BitVec 64)) (n! (_ BitVec 64)) (v1! (_ BitVec 64)) (v2! (_ BitVec 64)) (v3! (_ BitVec 64))) 
       (=> (and (inv c n v1 v2 v3) ( or ( and ( not ( = c n ) ) ( = c! ( bvadd c (_ bv1 64) ) ) ) ( and ( = c n ) ( = c! (_ bv1 64) ) ) )) (inv c! n! v1! v2! v3!))))
(assert (forall ((c (_ BitVec 64)) (n (_ BitVec 64)) (v1 (_ BitVec 64)) (v2 (_ BitVec 64)) (v3 (_ BitVec 64))) 
       (=> (inv c n v1 v2 v3) ( let ( ( a!1 ( or ( and ( not ( = c n ) ) ( or ( bvult c (_ bv0 64) ) ( bvugt c n ) ) ) ( and ( = c n ) ( bvugt n ( bvadd (_ bv1 64) ( bvnot (_ bv1 64) ) ) ) ) ) ) ) ( not a!1 ) ))))
(check-sat)
