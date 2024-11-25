(set-logic BV)

(synth-inv inv_fun ((flag (_ BitVec 64))(n (_ BitVec 64))(j (_ BitVec 64))(b (_ BitVec 64))))

(define-fun pre_fun ((flag (_ BitVec 64)) (n (_ BitVec 64)) (j (_ BitVec 64)) (b (_ BitVec 64))) Bool
       ( and ( = j #x0000000000000000 ) ( bvugt n #x0000000000000000 ) ( = b #x0000000000000000 ) ))
(define-fun trans_fun ((flag! (_ BitVec 64)) (n! (_ BitVec 64)) (j! (_ BitVec 64)) (b! (_ BitVec 64)) (flag (_ BitVec 64)) (n (_ BitVec 64)) (j (_ BitVec 64)) (b (_ BitVec 64))) Bool
       ( let ( ( a!1 ( or ( and ( bvult b n ) ( = flag #x0000000000000001 ) ( = j! ( bvadd j #x0000000000000001 ) ) ( = b! ( bvadd b #x0000000000000001 ) ) ( = n! n ) ( = flag! flag ) ) ( and ( bvult b n ) ( not ( = flag #x0000000000000001 ) ) ( = j! j ) ( = b! ( bvadd b #x0000000000000001 ) ) ( = n! n ) ( = flag! flag ) ) ( and ( bvuge b n ) ( = j! j ) ( = b! b ) ( = n! n ) ( = flag! flag ) ) ) ) ) ( and a!1 ) ))
(define-fun post_fun ((flag (_ BitVec 64)) (n (_ BitVec 64)) (j (_ BitVec 64)) (b (_ BitVec 64))) Bool
       ( or ( not ( = flag #x0000000000000001 ) ) ( not ( bvule n b ) ) ( = j n ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

