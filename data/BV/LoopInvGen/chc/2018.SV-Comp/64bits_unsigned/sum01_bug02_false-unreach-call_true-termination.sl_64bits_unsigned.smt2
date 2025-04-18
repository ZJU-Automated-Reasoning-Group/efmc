(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (n (_ BitVec 64)) (sn (_ BitVec 64))) 
       (=> ( and ( = j (_ bv10 64) ) ( = i (_ bv1 64) ) ( = sn (_ bv0 64) ) ( bvuge n (_ bv0 64) ) ) (inv i j n sn))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (n (_ BitVec 64)) (sn (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64)) (n! (_ BitVec 64)) (sn! (_ BitVec 64))) 
       (=> (and (inv i j n sn) ( and ( bvule i n ) ( ite ( bvult i j ) ( = sn! ( bvadd sn (_ bv2 64) ) ) ( = sn! sn ) ) ( = j! ( bvsub j (_ bv1 64) ) ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = n! n ) )) (inv i! j! n! sn!))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)) (n (_ BitVec 64)) (sn (_ BitVec 64))) 
       (=> (inv i j n sn) ( or ( bvule i n ) ( = sn ( bvmul n (_ bv2 64) ) ) ( = sn (_ bv0 64) ) ))))
(check-sat)
