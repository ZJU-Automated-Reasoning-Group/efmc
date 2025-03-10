(set-logic BV)

(synth-inv inv_fun ((z3 (_ BitVec 32))(z2 (_ BitVec 32))(z1 (_ BitVec 32))(m (_ BitVec 32))(n (_ BitVec 32))(x (_ BitVec 32))))

(define-fun pre_fun ((z3 (_ BitVec 32)) (z2 (_ BitVec 32)) (z1 (_ BitVec 32)) (m (_ BitVec 32)) (n (_ BitVec 32)) (x (_ BitVec 32))) Bool
       ( and ( = x #x00000000 ) ( = m #x00000000 ) ))
(define-fun trans_fun ((z3! (_ BitVec 32)) (z2! (_ BitVec 32)) (z1! (_ BitVec 32)) (m! (_ BitVec 32)) (n! (_ BitVec 32)) (x! (_ BitVec 32)) (z3 (_ BitVec 32)) (z2 (_ BitVec 32)) (z1 (_ BitVec 32)) (m (_ BitVec 32)) (n (_ BitVec 32)) (x (_ BitVec 32))) Bool
       ( let ( ( a!1 ( and ( bvult x n ) ( = x! ( bvadd x #x00000001 ) ) ( = n! n ) ) ) ) ( and ( or ( and a!1 ( = m! m ) ) ( and a!1 ( = m! x ) ) ) ) ))
(define-fun post_fun ((z3 (_ BitVec 32)) (z2 (_ BitVec 32)) (z1 (_ BitVec 32)) (m (_ BitVec 32)) (n (_ BitVec 32)) (x (_ BitVec 32))) Bool
       ( not ( and ( bvule n x ) ( not ( = n #x00000000 ) ) ( bvule n m ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

