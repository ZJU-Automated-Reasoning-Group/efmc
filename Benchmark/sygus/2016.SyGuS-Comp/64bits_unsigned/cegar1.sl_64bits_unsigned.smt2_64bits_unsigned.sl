(set-logic BV)

(synth-inv inv_fun ((y (_ BitVec 64))(x (_ BitVec 64))))

(define-fun pre_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( and ( bvuge x #x0000000000000000 ) ( bvule x #x0000000000000002 ) ( bvule y #x0000000000000002 ) ( bvuge y #x0000000000000000 ) ))
(define-fun trans_fun ((y! (_ BitVec 64)) (x! (_ BitVec 64)) (y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( and ( = x! ( bvadd x #x0000000000000002 ) ) ( = y! ( bvadd y #x0000000000000002 ) ) ))
(define-fun post_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( not ( and ( = x #x0000000000000004 ) ( = y #x0000000000000000 ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

