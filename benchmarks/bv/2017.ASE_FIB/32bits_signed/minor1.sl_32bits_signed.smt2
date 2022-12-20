(set-logic HORN)
(declare-fun inv ((_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32))) 
       (=> ( and ( bvsle x ( bvadd (_ bv1 32) ( bvnot (_ bv2 32) ) ) ) ( bvsge x ( bvadd (_ bv1 32) ( bvnot (_ bv3 32) ) ) ) ) (inv x))))
(assert (forall ((x (_ BitVec 32)) (x! (_ BitVec 32))) 
       (=> (and (inv x) ( or ( and ( = x! ( bvadd x (_ bv2 32) ) ) ( bvslt x (_ bv1 32) ) ) ( and ( = x! ( bvadd x (_ bv1 32) ) ) ( bvsge x (_ bv1 32) ) ) )) (inv x!))))
(assert (forall ((x (_ BitVec 32))) 
       (=> (inv x) ( and ( bvsge x ( bvadd (_ bv1 32) ( bvnot (_ bv5 32) ) ) ) ))))
(check-sat)
