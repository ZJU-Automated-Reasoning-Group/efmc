(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( and ( = x (_ bv0 32) ) ( = y (_ bv1 32) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv x y) ( and ( bvult x (_ bv6 32) ) ( = x! ( bvadd x (_ bv1 32) ) ) ( = y! ( bvmul y (_ bv2 32) ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv x y) ( or ( bvult x (_ bv6 32) ) ( not ( = y (_ bv64 32) ) ) ))))
(check-sat)
