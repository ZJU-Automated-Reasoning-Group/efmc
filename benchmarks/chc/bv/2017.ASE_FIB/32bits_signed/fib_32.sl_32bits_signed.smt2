(set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((k (_ BitVec 32)) (b (_ BitVec 32)) (i (_ BitVec 32)) (j (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> ( and ( bvsgt k (_ bv0 32) ) ( = i j ) ( = n (_ bv0 32) ) ( or ( = b (_ bv1 32) ) ( = b (_ bv0 32) ) ) ) (inv k b i j n))))
(assert (forall ((k (_ BitVec 32)) (b (_ BitVec 32)) (i (_ BitVec 32)) (j (_ BitVec 32)) (n (_ BitVec 32)) (k! (_ BitVec 32)) (b! (_ BitVec 32)) (i! (_ BitVec 32)) (j! (_ BitVec 32)) (n! (_ BitVec 32))) 
       (=> (and (inv k b i j n) ( or ( and ( bvsge n ( bvmul (_ bv2 32) k ) ) ( = k! k ) ( = b! b ) ( = i! i ) ( = j! j ) ( = n! n ) ) ( and ( bvslt n ( bvmul (_ bv2 32) k ) ) ( = b (_ bv1 32) ) ( = k! k ) ( = b! (_ bv0 32) ) ( = i! ( bvadd i (_ bv1 32) ) ) ( = j! j ) ( = n! ( bvadd n (_ bv1 32) ) ) ) ( and ( bvslt n ( bvmul (_ bv2 32) k ) ) ( not ( = b (_ bv1 32) ) ) ( = k! k ) ( = b! (_ bv1 32) ) ( = i! i ) ( = j! ( bvadd j (_ bv1 32) ) ) ( = n! ( bvadd n (_ bv1 32) ) ) ) )) (inv k! b! i! j! n!))))
(assert (forall ((k (_ BitVec 32)) (b (_ BitVec 32)) (i (_ BitVec 32)) (j (_ BitVec 32)) (n (_ BitVec 32))) 
       (=> (inv k b i j n) ( => ( bvsge n ( bvmul (_ bv2 32) k ) ) ( = i j ) ))))
(check-sat)
