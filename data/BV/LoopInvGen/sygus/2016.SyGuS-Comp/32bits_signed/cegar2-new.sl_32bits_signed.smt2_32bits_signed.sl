(set-logic BV)

(synth-inv inv_fun ((m (_ BitVec 32))(n (_ BitVec 32))(x (_ BitVec 32))))

(define-fun pre_fun ((m (_ BitVec 32)) (n (_ BitVec 32)) (x (_ BitVec 32))) Bool
       ( and ( = x #x00000001 ) ( = m #x00000001 ) ))
(define-fun trans_fun ((m! (_ BitVec 32)) (n! (_ BitVec 32)) (x! (_ BitVec 32)) (m (_ BitVec 32)) (n (_ BitVec 32)) (x (_ BitVec 32))) Bool
       ( let ( ( a!1 ( and ( bvslt x n ) ( = x! ( bvadd x #x00000001 ) ) ( = n! n ) ) ) ) ( and ( or ( and a!1 ( = m! m ) ) ( and a!1 ( = m! x ) ) ) ) ))
(define-fun post_fun ((m (_ BitVec 32)) (n (_ BitVec 32)) (x (_ BitVec 32))) Bool
       ( let ( ( a!1 ( and ( bvsle n x ) ( not ( bvsle n #x00000001 ) ) ( or ( bvsle n m ) ( not ( bvsle #x00000001 m ) ) ) ) ) ) ( not a!1 ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

