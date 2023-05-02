(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (c (_ BitVec 32)) (k (_ BitVec 32)) (turn (_ BitVec 32))) 
       (=> ( and ( = z k ) ( = x (_ bv0 32) ) ( = y (_ bv0 32) ) ( = turn (_ bv0 32) ) ) (inv x y z c k turn))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (c (_ BitVec 32)) (k (_ BitVec 32)) (turn (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (z! (_ BitVec 32)) (c! (_ BitVec 32)) (k! (_ BitVec 32)) (turn! (_ BitVec 32))) 
       (=> (and (inv x y z c k turn) ( let ( ( a!1 ( and ( = turn (_ bv1 32) ) ( = z ( bvsub ( bvadd k y ) c ) ) ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! ( bvadd y (_ bv1 32) ) ) ( = z! z ) ( = c! ( bvadd c (_ bv1 32) ) ) ( = k! k ) ( = turn! (_ bv1 32) ) ) ) ( a!2 ( not ( = z ( bvsub ( bvadd k y ) c ) ) ) ) ( a!3 ( and ( = turn (_ bv1 32) ) ( = z ( bvsub ( bvadd k y ) c ) ) ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! ( bvadd y (_ bv1 32) ) ) ( = z! z ) ( = c! ( bvadd c (_ bv1 32) ) ) ( = k! k ) ( = turn! (_ bv2 32) ) ) ) ) ( or ( and ( = turn (_ bv0 32) ) ( = x! x ) ( = y! y ) ( = z! z ) ( = c! (_ bv0 32) ) ( = k! k ) ( = turn! (_ bv1 32) ) ) ( and ( = turn (_ bv0 32) ) ( = x! x ) ( = y! y ) ( = z! z ) ( = c! (_ bv0 32) ) ( = k! k ) ( = turn! (_ bv2 32) ) ) a!1 ( and ( = turn (_ bv1 32) ) a!2 ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! ( bvsub y (_ bv1 32) ) ) ( = z! z ) ( = c! ( bvadd c (_ bv1 32) ) ) ( = k! k ) ( = turn! (_ bv1 32) ) ) a!3 ( and ( = turn (_ bv1 32) ) a!2 ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! ( bvsub y (_ bv1 32) ) ) ( = z! z ) ( = c! ( bvadd c (_ bv1 32) ) ) ( = k! k ) ( = turn! (_ bv2 32) ) ) ( and ( = turn (_ bv2 32) ) ( = x! ( bvsub x (_ bv1 32) ) ) ( = y! ( bvsub y (_ bv1 32) ) ) ( = z! z ) ( = c! c ) ( = k! k ) ( = turn! (_ bv2 32) ) ) ( and ( = turn (_ bv2 32) ) ( = x! ( bvsub x (_ bv1 32) ) ) ( = y! ( bvsub y (_ bv1 32) ) ) ( = z! z ) ( = c! c ) ( = k! k ) ( = turn! (_ bv3 32) ) ) ( and ( or ( bvugt turn (_ bv2 32) ) ( bvult turn (_ bv0 32) ) ) ( = x! x ) ( = y! y ) ( = z! ( bvadd x y ) ) ( = c! c ) ( = k! k ) ( = turn! (_ bv0 32) ) ) ) )) (inv x! y! z! c! k! turn!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (c (_ BitVec 32)) (k (_ BitVec 32)) (turn (_ BitVec 32))) 
       (=> (inv x y z c k turn) ( = x y ))))
(check-sat)
