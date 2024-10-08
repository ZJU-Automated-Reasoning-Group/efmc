(set-logic BV)

(synth-inv inv_fun ((y (_ BitVec 64))(x (_ BitVec 64))))

(define-fun pre_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( and ( = x #x0000000000000000 ) ( = y #x0000000000000000 ) ))
(define-fun trans_fun ((y! (_ BitVec 64)) (x! (_ BitVec 64)) (y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( let ( ( a!1 ( or ( and ( = x! ( bvadd x #x0000000000000001 ) ) ( = y! ( bvadd y #x0000000000000064 ) ) ) ( and ( bvuge x #x0000000000000004 ) ( = x! ( bvadd x #x0000000000000001 ) ) ( = y! ( bvadd y #x0000000000000001 ) ) ) ( and ( bvult x #x0000000000000000 ) ( = x! x ) ( = y! ( bvsub y #x0000000000000001 ) ) ) ( and ( = x! x ) ( = y! y ) ) ) ) ) ( and a!1 ) ))
(define-fun post_fun ((y (_ BitVec 64)) (x (_ BitVec 64))) Bool
       ( let ( ( a!1 ( not ( and ( = ( ( _ extract (_ bv63 64) (_ bv2 64) ) y ) #b00000000000000000000000000000000000000000000000000000000000000 ) ( bvule ( ( _ extract (_ bv1 64) (_ bv0 64) ) y ) #b10 ) ) ) ) ) ( or ( not ( bvule #x0000000000000004 x ) ) a!1 ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

