(set-logic BV)

(synth-inv inv_fun ((y (_ BitVec 64))(x (_ BitVec 64))))

(define-fun pre_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( = x ( bvadd #x0000000000000001 ( bvnot #x0000000000000032 ) ) ))
(define-fun trans_fun ((y! (_ BitVec 64)) (x! (_ BitVec 64)) (y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( let ( ( a!1 ( or ( and ( bvult x #x0000000000000000 ) ( = x! ( bvadd x y ) ) ( = y! ( bvadd y #x0000000000000001 ) ) ) ( and ( bvuge x #x0000000000000000 ) ( = x! x ) ( = y! y ) ) ) ) ) ( and a!1 ) ))
(define-fun post_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( t r u e ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

