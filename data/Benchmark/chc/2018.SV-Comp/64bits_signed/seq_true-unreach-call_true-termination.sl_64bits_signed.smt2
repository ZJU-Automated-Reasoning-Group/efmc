(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((n0 (_ BitVec 64)) (n1 (_ BitVec 64)) (i0 (_ BitVec 64)) (k (_ BitVec 64)) (i1 (_ BitVec 64)) (j1 (_ BitVec 64))) 
       (=> ( and ( bvsle ( bvsub (_ bv0 64) (_ bv1000000 64) ) n0 ) ( bvslt n0 (_ bv1000000 64) ) ( bvsle ( bvsub (_ bv0 64) (_ bv1000000 64) ) n1 ) ( bvslt n1 (_ bv1000000 64) ) ( = i1 (_ bv0 64) ) ( = j1 (_ bv0 64) ) ( = i0 (_ bv0 64) ) ( = k (_ bv0 64) ) ) (inv n0 n1 i0 k i1 j1))))
(assert (forall ((n0 (_ BitVec 64)) (n1 (_ BitVec 64)) (i0 (_ BitVec 64)) (k (_ BitVec 64)) (i1 (_ BitVec 64)) (j1 (_ BitVec 64)) (n0! (_ BitVec 64)) (n1! (_ BitVec 64)) (i0! (_ BitVec 64)) (k! (_ BitVec 64)) (i1! (_ BitVec 64)) (j1! (_ BitVec 64))) 
       (=> (and (inv n0 n1 i0 k i1 j1) ( or ( and ( bvslt i0 n0 ) ( = i0! ( bvadd i0 (_ bv1 64) ) ) ( = k! ( bvadd k (_ bv1 64) ) ) ( = n0! n0 ) ( = n1! n1 ) ( = i1! i1 ) ( = j1! j1 ) ) ( and ( bvsge i0 n0 ) ( bvslt i1 n1 ) ( = i1! ( bvadd i1 (_ bv1 64) ) ) ( = k! ( bvadd k (_ bv1 64) ) ) ( = n0! n0 ) ( = n1! n1 ) ( = i0! i0 ) ( = j1! j1 ) ) ( and ( bvsge i0 n0 ) ( bvsge i1 n1 ) ( bvslt j1 ( bvadd n0 n1 ) ) ( = j1! ( bvadd j1 (_ bv1 64) ) ) ( = k! ( bvsub k (_ bv1 64) ) ) ( = n0! n0 ) ( = n1! n1 ) ( = i0! i0 ) ( = i1! i1 ) ) )) (inv n0! n1! i0! k! i1! j1!))))
(assert (forall ((n0 (_ BitVec 64)) (n1 (_ BitVec 64)) (i0 (_ BitVec 64)) (k (_ BitVec 64)) (i1 (_ BitVec 64)) (j1 (_ BitVec 64))) 
       (=> (inv n0 n1 i0 k i1 j1) ( let ( ( a!1 ( not ( and ( bvsge i0 n0 ) ( bvsge i1 n1 ) ( bvslt j1 ( bvadd n0 n1 ) ) ) ) ) ) ( or a!1 ( bvsgt k (_ bv0 64) ) ) ))))
(check-sat)
