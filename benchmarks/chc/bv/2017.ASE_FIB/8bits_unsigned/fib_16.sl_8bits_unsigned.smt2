(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (i (_ BitVec 8)) (j (_ BitVec 8))) 
       (=> ( and ( = x i ) ( = y j ) ) (inv x y i j))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (i (_ BitVec 8)) (j (_ BitVec 8)) (x! (_ BitVec 8)) (y! (_ BitVec 8)) (i! (_ BitVec 8)) (j! (_ BitVec 8))) 
       (=> (and (inv x y i j) ( or ( and ( not ( = x (_ bv0 8) ) ) ( = x! ( bvsub x (_ bv1 8) ) ) ( = y! ( bvsub y (_ bv1 8) ) ) ( = i! i ) ( = j! j ) ) ( and ( = x (_ bv0 8) ) ( = x! x ) ( = y! y ) ( = i! i ) ( = j! j ) ) )) (inv x! y! i! j!))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (i (_ BitVec 8)) (j (_ BitVec 8))) 
       (=> (inv x y i j) ( => ( = x (_ bv0 8) ) ( or ( not ( = i j ) ) ( = y (_ bv0 8) ) ) ))))
(check-sat)
