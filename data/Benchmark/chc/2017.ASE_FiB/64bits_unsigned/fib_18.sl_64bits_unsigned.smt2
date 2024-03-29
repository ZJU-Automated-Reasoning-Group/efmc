(set-logic HORN)
(declare-fun inv ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) ) Bool)
(assert (forall ((b (_ BitVec 64)) (j (_ BitVec 64)) (n (_ BitVec 64)) (flag (_ BitVec 64))) 
       (=> ( and ( = j (_ bv0 64) ) ( bvugt n (_ bv0 64) ) ( = b (_ bv0 64) ) ) (inv b j n flag))))
(assert (forall ((b (_ BitVec 64)) (j (_ BitVec 64)) (n (_ BitVec 64)) (flag (_ BitVec 64)) (b! (_ BitVec 64)) (j! (_ BitVec 64)) (n! (_ BitVec 64)) (flag! (_ BitVec 64))) 
       (=> (and (inv b j n flag) ( or ( and ( bvult b n ) ( = flag (_ bv1 64) ) ( = j! ( bvadd j (_ bv1 64) ) ) ( = b! ( bvadd b (_ bv1 64) ) ) ( = n! n ) ( = flag! flag ) ) ( and ( bvult b n ) ( not ( = flag (_ bv1 64) ) ) ( = j! j ) ( = b! ( bvadd b (_ bv1 64) ) ) ( = n! n ) ( = flag! flag ) ) ( and ( bvuge b n ) ( = j! j ) ( = b! b ) ( = n! n ) ( = flag! flag ) ) )) (inv b! j! n! flag!))))
(assert (forall ((b (_ BitVec 64)) (j (_ BitVec 64)) (n (_ BitVec 64)) (flag (_ BitVec 64))) 
       (=> (inv b j n flag) ( => ( not ( bvult b n ) ) ( or ( not ( = flag (_ bv1 64) ) ) ( = j n ) ) ))))
(check-sat)
