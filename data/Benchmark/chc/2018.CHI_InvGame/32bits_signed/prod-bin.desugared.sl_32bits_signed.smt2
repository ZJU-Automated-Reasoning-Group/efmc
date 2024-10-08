(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((a (_ BitVec 32)) (b (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32))) 
       (=> ( and ( bvsge a (_ bv0 32) ) ( bvsge b (_ bv0 32) ) ( = x a ) ( = y b ) ( = z (_ bv0 32) ) ) (inv a b x y z))))
(assert (forall ((a (_ BitVec 32)) (b (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (a! (_ BitVec 32)) (b! (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32)) (z! (_ BitVec 32))) 
       (=> (and (inv a b x y z) ( let ( ( a!1 ( and ( not ( = (_ bv1 32) ( mod y (_ bv2 32) ) ) ) ( = x! ( bvmul (_ bv2 32) x ) ) ( = y! ( bvsdiv y (_ bv2 32) ) ) ( = z! z ) ) ) ) ( let ( ( a!2 ( or a!1 ( and ( = (_ bv1 32) ( mod y (_ bv2 32) ) ) ( = x! x ) ( = z! ( bvadd z x ) ) ( = y! ( bvsub y (_ bv1 32) ) ) ) ) ) ) ( and ( not ( = (_ bv0 32) y ) ) ( = a! a ) ( = b! b ) a!2 ) ) )) (inv a! b! x! y! z!))))
(assert (forall ((a (_ BitVec 32)) (b (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32))) 
       (=> (inv a b x y z) ( or ( not ( = y (_ bv0 32) ) ) ( = z ( bvmul a b ) ) ))))
(check-sat)
