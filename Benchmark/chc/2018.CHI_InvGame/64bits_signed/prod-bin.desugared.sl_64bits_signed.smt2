(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((a (_ BitVec 64)) (b (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64))) 
       (=> ( and ( bvsge a (_ bv0 64) ) ( bvsge b (_ bv0 64) ) ( = x a ) ( = y b ) ( = z (_ bv0 64) ) ) (inv a b x y z))))
(assert (forall ((a (_ BitVec 64)) (b (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64)) (a! (_ BitVec 64)) (b! (_ BitVec 64)) (x! (_ BitVec 64)) (y! (_ BitVec 64)) (z! (_ BitVec 64))) 
       (=> (and (inv a b x y z) ( let ( ( a!1 ( and ( not ( = (_ bv1 64) ( mod y (_ bv2 64) ) ) ) ( = x! ( bvmul (_ bv2 64) x ) ) ( = y! ( bvsdiv y (_ bv2 64) ) ) ( = z! z ) ) ) ) ( let ( ( a!2 ( or a!1 ( and ( = (_ bv1 64) ( mod y (_ bv2 64) ) ) ( = x! x ) ( = z! ( bvadd z x ) ) ( = y! ( bvsub y (_ bv1 64) ) ) ) ) ) ) ( and ( not ( = (_ bv0 64) y ) ) ( = a! a ) ( = b! b ) a!2 ) ) )) (inv a! b! x! y! z!))))
(assert (forall ((a (_ BitVec 64)) (b (_ BitVec 64)) (x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64))) 
       (=> (inv a b x y z) ( or ( not ( = y (_ bv0 64) ) ) ( = z ( bvmul a b ) ) ))))
(check-sat)
