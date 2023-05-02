(set-logic BV)

(synth-inv inv_fun ((m (_ BitVec 64))(n (_ BitVec 64))(x (_ BitVec 64))))

(define-fun pre_fun ((m (_ BitVec 64)) (n (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( and ( = x #x0000000000000000 ) ( = m #x0000000000000000 ) ))
(define-fun trans_fun ((m! (_ BitVec 64)) (n! (_ BitVec 64)) (x! (_ BitVec 64)) (m (_ BitVec 64)) (n (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( let ( ( a!1 ( and ( bvult x n ) ( = x! ( bvadd x #x0000000000000001 ) ) ( = n! n ) ) ) ) ( and ( or ( and a!1 ( = m! m ) ) ( and a!1 ( = m! x ) ) ) ) ))
(define-fun post_fun ((m (_ BitVec 64)) (n (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( not ( and ( bvule n x ) ( not ( = n #x0000000000000000 ) ) ( bvule n m ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

