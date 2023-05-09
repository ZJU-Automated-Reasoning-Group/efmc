(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) ) Bool)
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (i (_ BitVec 8)) (j (_ BitVec 8))) 
       (=> ( and ( = x (_ bv0 8) ) ( = y (_ bv0 8) ) ( = j (_ bv0 8) ) ( = i (_ bv0 8) ) ) (inv x y i j))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (i (_ BitVec 8)) (j (_ BitVec 8)) (x! (_ BitVec 8)) (y! (_ BitVec 8)) (i! (_ BitVec 8)) (j! (_ BitVec 8))) 
       (=> (and (inv x y i j) ( let ( ( a!1 ( or ( = j! ( bvadd y! j ) ) ( = j! ( bvadd ( bvadd y! j ) (_ bv1 8) ) ) ) ) ) ( and ( = x! ( bvadd x (_ bv1 8) ) ) ( = y! ( bvadd y (_ bv1 8) ) ) ( = i! ( bvadd x! i ) ) a!1 ) )) (inv x! y! i! j!))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (i (_ BitVec 8)) (j (_ BitVec 8))) 
       (=> (inv x y i j) ( bvsge j i ))))
(check-sat)
