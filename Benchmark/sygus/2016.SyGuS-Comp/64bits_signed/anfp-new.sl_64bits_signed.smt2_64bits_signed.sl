(set-logic BV)

(synth-inv inv_fun ((y (_ BitVec 64))(x (_ BitVec 64))))

(define-fun pre_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( and ( = x #x0000000000000001 ) ( = y #x0000000000000000 ) ))
(define-fun trans_fun ((y! (_ BitVec 64)) (x! (_ BitVec 64)) (y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( and ( bvslt y #x00000000000186a0 ) ( = x! ( bvadd x y ) ) ( = y! ( bvadd y #x0000000000000001 ) ) ))
(define-fun post_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( not ( and ( bvsle #x00000000000186a0 y ) ( not ( bvsle y x ) ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

