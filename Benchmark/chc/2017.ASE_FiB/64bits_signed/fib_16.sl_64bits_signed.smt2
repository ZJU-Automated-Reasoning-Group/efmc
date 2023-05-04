(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (i (_ BitVec 64)) (j (_ BitVec 64))) 
       (=> ( and ( = x i ) ( = y j ) ) (inv x y i j))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (i (_ BitVec 64)) (j (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64))) 
       (=> (and (inv x y i j) ( or ( and ( not ( = x (_ bv0 64) ) ) ( = x! ( bvsub x (_ bv1 64) ) ) ( = y! ( bvsub y (_ bv1 64) ) ) ( = i! i ) ( = j! j ) ) ( and ( = x (_ bv0 64) ) ( = x! x ) ( = y! y ) ( = i! i ) ( = j! j ) ) )) (inv x! y! i! j!))))
(assert (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (i (_ BitVec 64)) (j (_ BitVec 64))) 
       (=> (inv x y i j) ( => ( = x (_ bv0 64) ) ( or ( not ( = i j ) ) ( = y (_ bv0 64) ) ) ))))
(check-sat)