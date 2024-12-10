(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((k (_ BitVec 64)) (b (_ BitVec 64)) (i (_ BitVec 64)) (j (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> ( and ( bvugt k (_ bv0 64) ) ( = i j ) ( = n (_ bv0 64) ) ( or ( = b (_ bv1 64) ) ( = b (_ bv0 64) ) ) ) (inv k b i j n))))
(assert (forall ((k (_ BitVec 64)) (b (_ BitVec 64)) (i (_ BitVec 64)) (j (_ BitVec 64)) (n (_ BitVec 64)) (k! (_ BitVec 64)) (b! (_ BitVec 64)) (i! (_ BitVec 64)) (j! (_ BitVec 64)) (n! (_ BitVec 64))) 
       (=> (and (inv k b i j n) ( or ( and ( bvuge n ( bvmul (_ bv2 64) k ) ) ( = k! k ) ( = b! b ) ( = i! i ) ( = j! j ) ( = n! n ) ) ( and ( bvult n ( bvmul (_ bv2 64) k ) ) ( = b (_ bv1 64) ) ( = k! k ) ( = b! (_ bv0 64) ) ( = i! ( bvadd i (_ bv1 64) ) ) ( = j! j ) ( = n! ( bvadd n (_ bv1 64) ) ) ) ( and ( bvult n ( bvmul (_ bv2 64) k ) ) ( not ( = b (_ bv1 64) ) ) ( = k! k ) ( = b! (_ bv1 64) ) ( = i! i ) ( = j! ( bvadd j (_ bv1 64) ) ) ( = n! ( bvadd n (_ bv1 64) ) ) ) )) (inv k! b! i! j! n!))))
(assert (forall ((k (_ BitVec 64)) (b (_ BitVec 64)) (i (_ BitVec 64)) (j (_ BitVec 64)) (n (_ BitVec 64))) 
       (=> (inv k b i j n) ( => ( bvuge n ( bvmul (_ bv2 64) k ) ) ( = i j ) ))))
(check-sat)