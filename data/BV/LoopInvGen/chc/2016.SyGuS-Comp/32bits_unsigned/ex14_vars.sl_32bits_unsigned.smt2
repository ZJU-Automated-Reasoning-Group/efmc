(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (n (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> ( = x (_ bv1 32) ) (inv x y n v1 v2 v3))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (n (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (n! (_ BitVec 32)) (v1! (_ BitVec 32)) (v2! (_ BitVec 32)) (v3! (_ BitVec 32))) 
       (=> (and (inv x y n v1 v2 v3) ( and ( bvule x n ) ( = y! ( bvsub n x ) ) ( = x! ( bvadd x (_ bv1 32) ) ) )) (inv x! y! n! v1! v2! v3!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (n (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (v3 (_ BitVec 32))) 
       (=> (inv x y n v1 v2 v3) ( not ( and ( bvule x n ) ( = y ( bvsub n x ) ) ( or ( bvuge y n ) ( bvugt (_ bv0 32) y ) ) ) ))))
(check-sat)