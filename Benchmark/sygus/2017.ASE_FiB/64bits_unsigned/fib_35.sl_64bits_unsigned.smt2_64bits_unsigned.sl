(set-logic BV)

(synth-inv inv_fun ((n (_ BitVec 64))(x (_ BitVec 64))))

(define-fun pre_fun ((n (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( and ( bvugt n #x0000000000000000 ) ( = x #x0000000000000000 ) ))
(define-fun trans_fun ((n! (_ BitVec 64)) (x! (_ BitVec 64)) (n (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( let ( ( a!1 ( or ( and ( bvuge x n ) ( = x! x ) ( = n! n ) ) ( and ( bvult x n ) ( = x! ( bvadd x #x0000000000000001 ) ) ( = n! n ) ) ) ) ) ( and a!1 ) ))
(define-fun post_fun ((n (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( or ( not ( bvule n x ) ) ( = x n ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
