(set-logic BV)

(synth-inv inv_fun ((cnt (_ BitVec 32))(res (_ BitVec 32))(b (_ BitVec 32))(a (_ BitVec 32))))

(define-fun pre_fun ((cnt (_ BitVec 32)) (res (_ BitVec 32)) (b (_ BitVec 32)) (a (_ BitVec 32))) Bool
       ( and ( bvule a #x000f4240 ) ( bvule #x00000000 b ) ( bvule b #x000f4240 ) ( = res a ) ( = cnt b ) ))
(define-fun trans_fun ((cnt! (_ BitVec 32)) (res! (_ BitVec 32)) (b! (_ BitVec 32)) (a! (_ BitVec 32)) (cnt (_ BitVec 32)) (res (_ BitVec 32)) (b (_ BitVec 32)) (a (_ BitVec 32))) Bool
       ( and ( bvugt cnt #x00000000 ) ( = cnt! ( bvsub cnt #x00000001 ) ) ( = res! ( bvadd res #x00000001 ) ) ( = a! a ) ( = b! b ) ))
(define-fun post_fun ((cnt (_ BitVec 32)) (res (_ BitVec 32)) (b (_ BitVec 32)) (a (_ BitVec 32))) Bool
       ( or ( not ( = cnt #x00000000 ) ) ( = res ( bvadd a b ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
