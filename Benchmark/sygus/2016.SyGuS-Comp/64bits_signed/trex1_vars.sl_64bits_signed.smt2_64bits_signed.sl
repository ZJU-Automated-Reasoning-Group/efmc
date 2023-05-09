(set-logic BV)

(synth-inv inv_fun ((z3 (_ BitVec 64))(z2 (_ BitVec 64))(z1 (_ BitVec 64))(y (_ BitVec 64))(x (_ BitVec 64))))

(define-fun pre_fun ((z3 (_ BitVec 64)) (z2 (_ BitVec 64)) (z1 (_ BitVec 64)) (y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( = x #x0000000000000001 ))
(define-fun trans_fun ((z3! (_ BitVec 64)) (z2! (_ BitVec 64)) (z1! (_ BitVec 64)) (y! (_ BitVec 64)) (x! (_ BitVec 64)) (z3 (_ BitVec 64)) (z2 (_ BitVec 64)) (z1 (_ BitVec 64)) (y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( and ( bvslt x y ) ( = x! ( bvadd x x ) ) ))
(define-fun post_fun ((z3 (_ BitVec 64)) (z2 (_ BitVec 64)) (z1 (_ BitVec 64)) (y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( or ( not ( bvsle y x ) ) ( bvsle #x0000000000000001 x ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

