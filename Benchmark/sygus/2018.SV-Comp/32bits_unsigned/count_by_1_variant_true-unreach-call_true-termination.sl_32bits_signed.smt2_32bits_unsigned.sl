(set-logic BV)

(synth-inv inv_fun ((i (_ BitVec 32))))

(define-fun pre_fun ((i (_ BitVec 32))) Bool
       ( = i #x00000000 ))
(define-fun trans_fun ((i! (_ BitVec 32)) (i (_ BitVec 32))) Bool
       ( and ( not ( = i #x000f4240 ) ) ( = i! ( bvadd i #x00000001 ) ) ))
(define-fun post_fun ((i (_ BitVec 32))) Bool
       ( or ( not ( = i #x000f4240 ) ) ( bvsle i #x000f4240 ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

