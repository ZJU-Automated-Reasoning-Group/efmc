(set-logic BV)

(synth-inv inv_fun ((n (_ BitVec 64))(sum (_ BitVec 64))(i (_ BitVec 64))))

(define-fun pre_fun ((n (_ BitVec 64)) (sum (_ BitVec 64)) (i (_ BitVec 64))) Bool
       ( and ( = sum #x0000000000000000 ) ( bvsge n #x0000000000000000 ) ( = i #x0000000000000000 ) ))
(define-fun trans_fun ((n! (_ BitVec 64)) (sum! (_ BitVec 64)) (i! (_ BitVec 64)) (n (_ BitVec 64)) (sum (_ BitVec 64)) (i (_ BitVec 64))) Bool
       ( let ( ( a!1 ( or ( and ( bvslt i n ) ( = i! ( bvadd i #x0000000000000001 ) ) ( = sum! ( bvadd sum i ) ) ( = n! n ) ) ( and ( bvsge i n ) ( = i! i ) ( = sum! sum ) ( = n! n ) ) ) ) ) ( and a!1 ) ))
(define-fun post_fun ((n (_ BitVec 64)) (sum (_ BitVec 64)) (i (_ BitVec 64))) Bool
       ( or ( not ( bvsle n i ) ) ( bvsle #x0000000000000000 sum ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

