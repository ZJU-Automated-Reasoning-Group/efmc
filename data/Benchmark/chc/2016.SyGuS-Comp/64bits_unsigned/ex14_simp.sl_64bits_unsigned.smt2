(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> ( = x (_ bv1 64) ) (inv x y n))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (n (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (n! (_ BitVec 64))) 
       (=> (and (inv x y n) ( and ( bvule x n ) ( = y! ( bvsub n x ) ) ( = x! ( bvadd x (_ bv1 64) ) ) )) (inv x! y! n!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> (inv x y n) ( not ( and ( bvule x n ) ( = y ( bvsub n x ) ) ( or ( bvuge y n ) ( bvugt (_ bv0 64) y ) ) ) ))))
(check-sat)
