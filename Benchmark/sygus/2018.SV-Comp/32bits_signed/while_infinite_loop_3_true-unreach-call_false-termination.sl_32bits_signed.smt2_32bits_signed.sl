(set-logic BV)

(synth-inv inv_fun ((x (_ BitVec 32))))

(define-fun pre_fun ((x (_ BitVec 32))) Bool
       ( = x #x00000000 ))
(define-fun trans_fun ((x! (_ BitVec 32)) (x (_ BitVec 32))) Bool
       ( and ( = x! #x00000000 ) ))
(define-fun post_fun ((x (_ BitVec 32))) Bool
       ( = x #x00000000 ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

