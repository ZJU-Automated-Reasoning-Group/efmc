(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((n (_ BitVec 32)) (sum (_ BitVec 32)) (i (_ BitVec 32))) 
       (=> ( and ( bvule (_ bv1 32) n ) ( bvule n (_ bv1000 32) ) ( = sum (_ bv0 32) ) ( = i (_ bv1 32) ) ) (inv n sum i))))
(assert (forall ((n (_ BitVec 32)) (sum (_ BitVec 32)) (i (_ BitVec 32)) (n! (_ BitVec 32)) (sum! (_ BitVec 32)) (i! (_ BitVec 32))) 
       (=> (and (inv n sum i) ( and ( bvule i n ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = sum! ( bvadd sum i ) ) ( = n! n ) )) (inv n! sum! i!))))
(assert (forall ((n (_ BitVec 32)) (sum (_ BitVec 32)) (i (_ BitVec 32))) 
       (=> (inv n sum i) ( or ( bvule i n ) ( = ( bvmul sum (_ bv2 32) ) ( bvmul n ( bvadd n (_ bv1 32) ) ) ) ))))
(check-sat)
