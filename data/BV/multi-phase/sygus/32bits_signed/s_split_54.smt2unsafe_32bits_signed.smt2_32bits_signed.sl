(set-logic BV)

(synth-inv inv_fun ((z (_ BitVec 32))(x (_ BitVec 32))(y (_ BitVec 32))))

(define-fun pre_fun ((z (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) Bool
       ( and ( = x #x00000000 ) ( = y #x00001f40 ) ( = z #x00000000 ) ))
(define-fun trans_fun ((z! (_ BitVec 32)) (y! (_ BitVec 32)) (x! (_ BitVec 32)) (z (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) Bool
       ( and ( = x! ( bvadd x #x00000001 ) ) ( = y! ( ite ( bvsge x #x00001f40 ) ( bvadd y #x00000001 ) ( bvsub y #x00000001 ) ) ) ( = z! ( ite ( bvslt x #x00001f40 ) ( bvadd z #x00000001 ) ( bvsub z #x00000001 ) ) ) ))
(define-fun post_fun ((z (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) Bool
       ( not ( and ( = x #x00003e80 ) ( = y #x00001f40 ) ( = z #x00000000 ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

