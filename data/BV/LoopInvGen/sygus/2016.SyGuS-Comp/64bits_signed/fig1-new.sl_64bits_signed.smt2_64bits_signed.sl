(set-logic BV)

(synth-inv inv_fun ((y (_ BitVec 64))(x (_ BitVec 64))))

(define-fun pre_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( = x ( bvadd #x0000000000000001 ( bvnot #x0000000000001388 ) ) ))
(define-fun trans_fun ((y! (_ BitVec 64)) (x! (_ BitVec 64)) (y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( and ( bvslt x #x0000000000000000 ) ( = x! ( bvadd x y ) ) ( = y! ( bvadd y #x0000000000000001 ) ) ))
(define-fun post_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( not ( and ( bvsle #x0000000000000000 x ) ( bvsle y #x0000000000000000 ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

