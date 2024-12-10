(set-logic BV)

(synth-inv inv_fun ((w (_ BitVec 32))(x (_ BitVec 32))(y (_ BitVec 32))(z (_ BitVec 32))))

(define-fun pre_fun ((w (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32))) Bool
       ( and ( = x #x00000000 ) ( = y #x00000000 ) ( = z #x00000000 ) ( = w #x00000000 ) ))
(define-fun trans_fun ((w! (_ BitVec 32)) (z! (_ BitVec 32)) (y! (_ BitVec 32)) (x! (_ BitVec 32)) (w (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32))) Bool
       ( let ( ( a!1 ( ite ( bvsgt ( bvsub y ( bvmul #x0000000a x ) ) #x00000000 ) ( bvadd z #x00000001 ) z ) ) ( a!2 ( ite ( bvsgt ( bvsub y ( bvmul #x0000000a x ) ) #x00000000 ) w ( bvadd w #x00000001 ) ) ) ) ( and ( = x! ( bvadd x #x00000001 ) ) ( = y! ( bvadd y x ) ) ( = z! a!1 ) ( = w! a!2 ) ) ))
(define-fun post_fun ((w (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32))) Bool
       ( not ( and ( not ( bvsle x #x00000064 ) ) ( bvsle z w ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

