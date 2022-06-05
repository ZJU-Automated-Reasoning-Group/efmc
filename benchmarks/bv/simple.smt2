(declare-fun inv ((_ BitVec 8)) Bool)
(assert
 (forall ((i (_ BitVec 8)) )(let (($x12 (inv i)))
 (let (($x13 (= i (_ bv0 8))))
 (=> $x13 $x12))))
 )
(assert
 (forall ((i (_ BitVec 8)) (i! (_ BitVec 8)) )(let (($x12 (inv i!)))
 (=> (and (inv i) (bvult i (_ bv10 8)) (= i! (bvadd i (_ bv1 8)))) $x12)))
 )
(assert
 (forall ((i (_ BitVec 8)) )(let (($x56 (= i (_ bv10 8))))
 (=> (and (inv i) (bvuge i (_ bv10 8))) $x56)))
 )
(check-sat)