(set-logic BV)

(synth-inv inv_fun ((n (_ BitVec 32))(y (_ BitVec 32))(x (_ BitVec 32))(i (_ BitVec 32))))

(define-fun pre_fun ((n (_ BitVec 32)) (y (_ BitVec 32)) (x (_ BitVec 32)) (i (_ BitVec 32))) Bool
       ( and ( = i #x00000000 ) ( = x #x00000000 ) ( = y #x00000000 ) ( bvugt n #x00000000 ) ))
(define-fun trans_fun ((n! (_ BitVec 32)) (y! (_ BitVec 32)) (x! (_ BitVec 32)) (i! (_ BitVec 32)) (n (_ BitVec 32)) (y (_ BitVec 32)) (x (_ BitVec 32)) (i (_ BitVec 32))) Bool
       ( and ( bvult i n ) ( = x! ( bvadd x y! ) ) ( not ( = y! #x00000000 ) ) ( = i! i ) ( = n! n ) ))
(define-fun post_fun ((n (_ BitVec 32)) (y (_ BitVec 32)) (x (_ BitVec 32)) (i (_ BitVec 32))) Bool
       ( or ( not ( bvule n i ) ) ( = x #x00000000 ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

