(set-logic BV)

(synth-inv inv_fun ((b (_ BitVec 64))(a (_ BitVec 64))(n (_ BitVec 64))(i (_ BitVec 64))))

(define-fun pre_fun ((b (_ BitVec 64)) (a (_ BitVec 64)) (n (_ BitVec 64)) (i (_ BitVec 64))) Bool
       ( and ( = i #x0000000000000000 ) ( = a #x0000000000000000 ) ( = b #x0000000000000000 ) ( bvsge n #x0000000000000000 ) ))
(define-fun trans_fun ((b! (_ BitVec 64)) (a! (_ BitVec 64)) (n! (_ BitVec 64)) (i! (_ BitVec 64)) (b (_ BitVec 64)) (a (_ BitVec 64)) (n (_ BitVec 64)) (i (_ BitVec 64))) Bool
       ( let ( ( a!1 ( or ( and ( = a! ( bvadd a #x0000000000000001 ) ) ( = b! ( bvadd b #x0000000000000002 ) ) ) ( and ( = a! ( bvadd a #x0000000000000002 ) ) ( = b! ( bvadd b #x0000000000000001 ) ) ) ) ) ) ( and ( bvslt i n ) a!1 ( = i! ( bvadd i #x0000000000000001 ) ) ( = n! n ) ) ))
(define-fun post_fun ((b (_ BitVec 64)) (a (_ BitVec 64)) (n (_ BitVec 64)) (i (_ BitVec 64))) Bool
       ( or ( not ( bvsle n i ) ) ( = ( bvadd a b ) ( bvmul #x0000000000000003 n ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

