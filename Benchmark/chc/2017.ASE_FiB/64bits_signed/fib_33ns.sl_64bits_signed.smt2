(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64)) (c (_ BitVec 64)) (k (_ BitVec 64)) (turn (_ BitVec 64))) 
       (=> ( and ( = z k ) ( = x (_ bv0 64) ) ( = y (_ bv0 64) ) ( = turn (_ bv0 64) ) ) (inv x y z c k turn))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64)) (c (_ BitVec 64)) (k (_ BitVec 64)) (turn (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (z! (_ BitVec 64)) (c! (_ BitVec 64)) (k! (_ BitVec 64)) (turn! (_ BitVec 64))) 
       (=> (and (inv x y z c k turn) ( let ( ( a!1 ( and ( = turn (_ bv1 64) ) ( = z ( bvsub ( bvadd k y ) c ) ) ( = x! ( bvadd x (_ bv1 64) ) ) ( = y! ( bvadd y (_ bv1 64) ) ) ( = z! z ) ( = c! ( bvadd c (_ bv1 64) ) ) ( = k! k ) ( = turn! (_ bv1 64) ) ) ) ( a!2 ( not ( = z ( bvsub ( bvadd k y ) c ) ) ) ) ( a!3 ( and ( = turn (_ bv1 64) ) ( = z ( bvsub ( bvadd k y ) c ) ) ( = x! ( bvadd x (_ bv1 64) ) ) ( = y! ( bvadd y (_ bv1 64) ) ) ( = z! z ) ( = c! ( bvadd c (_ bv1 64) ) ) ( = k! k ) ( = turn! (_ bv2 64) ) ) ) ) ( or ( and ( = turn (_ bv0 64) ) ( = x! x ) ( = y! y ) ( = z! z ) ( = c! (_ bv0 64) ) ( = k! k ) ( = turn! (_ bv1 64) ) ) ( and ( = turn (_ bv0 64) ) ( = x! x ) ( = y! y ) ( = z! z ) ( = c! (_ bv0 64) ) ( = k! k ) ( = turn! (_ bv2 64) ) ) a!1 ( and ( = turn (_ bv1 64) ) a!2 ( = x! ( bvadd x (_ bv1 64) ) ) ( = y! ( bvsub y (_ bv1 64) ) ) ( = z! z ) ( = c! ( bvadd c (_ bv1 64) ) ) ( = k! k ) ( = turn! (_ bv1 64) ) ) a!3 ( and ( = turn (_ bv1 64) ) a!2 ( = x! ( bvadd x (_ bv1 64) ) ) ( = y! ( bvsub y (_ bv1 64) ) ) ( = z! z ) ( = c! ( bvadd c (_ bv1 64) ) ) ( = k! k ) ( = turn! (_ bv2 64) ) ) ( and ( = turn (_ bv2 64) ) ( = x! ( bvsub x (_ bv1 64) ) ) ( = y! ( bvsub y (_ bv1 64) ) ) ( = z! z ) ( = c! c ) ( = k! k ) ( = turn! (_ bv2 64) ) ) ( and ( = turn (_ bv2 64) ) ( = x! ( bvsub x (_ bv1 64) ) ) ( = y! ( bvsub y (_ bv1 64) ) ) ( = z! z ) ( = c! c ) ( = k! k ) ( = turn! (_ bv3 64) ) ) ( and ( or ( bvsgt turn (_ bv2 64) ) ( bvslt turn (_ bv0 64) ) ) ( = x! x ) ( = y! y ) ( = z! ( bvadd x y ) ) ( = c! c ) ( = k! k ) ( = turn! (_ bv0 64) ) ) ) )) (inv x! y! z! c! k! turn!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64)) (c (_ BitVec 64)) (k (_ BitVec 64)) (turn (_ BitVec 64))) 
       (=> (inv x y z c k turn) ( = x y ))))
(check-sat)