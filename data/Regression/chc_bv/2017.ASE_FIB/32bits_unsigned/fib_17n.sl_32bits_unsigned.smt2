(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((k (_ BitVec 32)) (i (_ BitVec 32)) (j (_ BitVec 32)) (n (_ BitVec 32)) (turn (_ BitVec 32))) 
       (=> ( and ( = k (_ bv1 32) ) ( = i (_ bv1 32) ) ( = j (_ bv0 32) ) ( = turn (_ bv0 32) ) ) (inv k i j n turn))))
(assert (forall ((k (_ BitVec 32)) (i (_ BitVec 32)) (j (_ BitVec 32)) (n (_ BitVec 32)) (turn (_ BitVec 32)) (k! (_ BitVec 32)) (i! (_ BitVec 32)) (j! (_ BitVec 32)) (n! (_ BitVec 32)) (turn! (_ BitVec 32))) 
       (=> (and (inv k i j n turn) ( let ( ( a!1 ( and ( = turn (_ bv1 32) ) ( bvult j i ) ( = k! ( bvsub ( bvadd k i ) j ) ) ( = i! i ) ( = j! ( bvadd j (_ bv1 32) ) ) ( = n! n ) ( = turn! turn ) ) ) ) ( or ( and ( = turn (_ bv0 32) ) ( bvult i n ) ( = k! k ) ( = i! i ) ( = j! (_ bv0 32) ) ( = n! n ) ( = turn! (_ bv1 32) ) ) ( and ( = turn (_ bv0 32) ) ( bvuge i n ) ( = k! k ) ( = i! i ) ( = j! j ) ( = n! n ) ( = turn! (_ bv3 32) ) ) a!1 ( and ( = turn (_ bv1 32) ) ( bvuge j i ) ( = k! k ) ( = i! i ) ( = j! j ) ( = n! n ) ( = turn! (_ bv2 32) ) ) ( and ( = turn (_ bv2 32) ) ( = k! k ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = j! j ) ( = n! n ) ( = turn! (_ bv0 32) ) ) ( and ( bvuge turn (_ bv3 32) ) ( = k! k ) ( = i! i ) ( = j! j ) ( = n! n ) ( = turn! turn ) ) ( and ( bvult turn (_ bv0 32) ) ( = k! k ) ( = i! i ) ( = j! j ) ( = n! n ) ( = turn! turn ) ) ) )) (inv k! i! j! n! turn!))))
(assert (forall ((k (_ BitVec 32)) (i (_ BitVec 32)) (j (_ BitVec 32)) (n (_ BitVec 32)) (turn (_ BitVec 32))) 
       (=> (inv k i j n turn) ( => ( = turn (_ bv3 32) ) ( bvuge k n ) ))))
(check-sat)
