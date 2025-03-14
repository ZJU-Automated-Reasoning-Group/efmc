(set-logic BV)

(synth-inv inv_fun ((sn (_ BitVec 32))(n (_ BitVec 32))(j (_ BitVec 32))(i (_ BitVec 32))))

(define-fun pre_fun ((sn (_ BitVec 32)) (n (_ BitVec 32)) (j (_ BitVec 32)) (i (_ BitVec 32))) Bool
       ( and ( = j #x0000000a ) ( = i #x00000001 ) ( = sn #x00000000 ) ( bvuge n #x00000000 ) ))
(define-fun trans_fun ((sn! (_ BitVec 32)) (n! (_ BitVec 32)) (j! (_ BitVec 32)) (i! (_ BitVec 32)) (sn (_ BitVec 32)) (n (_ BitVec 32)) (j (_ BitVec 32)) (i (_ BitVec 32))) Bool
       ( and ( bvule i n ) ( ite ( bvult i j ) ( = sn! ( bvadd sn #x00000002 ) ) ( = sn! sn ) ) ( = j! ( bvsub j #x00000001 ) ) ( = i! ( bvadd i #x00000001 ) ) ( = n! n ) ))
(define-fun post_fun ((sn (_ BitVec 32)) (n (_ BitVec 32)) (j (_ BitVec 32)) (i (_ BitVec 32))) Bool
       ( or ( = sn #x00000000 ) ( bvule i n ) ( = sn ( bvmul #x00000002 n ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

