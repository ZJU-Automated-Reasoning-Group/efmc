(set-logic BV)

(synth-inv inv_fun ((k (_ BitVec 64))(i (_ BitVec 64))))

(define-fun pre_fun ((k (_ BitVec 64)) (i (_ BitVec 64))) Bool
       ( and ( = i #x0000000000000000 ) ( = k #x0000000000000000 ) ))
(define-fun trans_fun ((k! (_ BitVec 64)) (i! (_ BitVec 64)) (k (_ BitVec 64)) (i (_ BitVec 64))) Bool
       ( and ( bvult i #x00000000000003e8 ) ( = i! ( bvadd i #x0000000000000001 ) ) ( = k! ( bvadd k ( bvmul i! i! ) ) ) ))
(define-fun post_fun ((k (_ BitVec 64)) (i (_ BitVec 64))) Bool
       ( or ( not ( bvule #x00000000000003e8 i ) ) ( bvule #x00000000000f4240 k ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

