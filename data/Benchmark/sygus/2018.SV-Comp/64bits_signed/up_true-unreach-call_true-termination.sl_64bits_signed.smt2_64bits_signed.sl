(set-logic BV)

(synth-inv inv_fun ((j (_ BitVec 64))(k (_ BitVec 64))(i (_ BitVec 64))(n (_ BitVec 64))))

(define-fun pre_fun ((j (_ BitVec 64)) (k (_ BitVec 64)) (i (_ BitVec 64)) (n (_ BitVec 64))) Bool
       ( and ( = i #x0000000000000000 ) ( = k #x0000000000000000 ) ( = j #x0000000000000000 ) ))
(define-fun trans_fun ((j! (_ BitVec 64)) (k! (_ BitVec 64)) (i! (_ BitVec 64)) (n! (_ BitVec 64)) (j (_ BitVec 64)) (k (_ BitVec 64)) (i (_ BitVec 64)) (n (_ BitVec 64))) Bool
       ( let ( ( a!1 ( or ( and ( bvslt i n ) ( = i! ( bvadd i #x0000000000000001 ) ) ( = k! ( bvadd k #x0000000000000001 ) ) ( = n! n ) ( = j! j ) ) ( and ( bvsge i n ) ( bvslt j n ) ( = j! ( bvadd j #x0000000000000001 ) ) ( = k! ( bvsub k #x0000000000000001 ) ) ( = n! n ) ( = i! i ) ) ) ) ) ( and a!1 ) ))
(define-fun post_fun ((j (_ BitVec 64)) (k (_ BitVec 64)) (i (_ BitVec 64)) (n (_ BitVec 64))) Bool
       ( let ( ( a!1 ( not ( and ( bvsle n i ) ( not ( bvsle n j ) ) ) ) ) ) ( or a!1 ( not ( bvsle k #x0000000000000000 ) ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

