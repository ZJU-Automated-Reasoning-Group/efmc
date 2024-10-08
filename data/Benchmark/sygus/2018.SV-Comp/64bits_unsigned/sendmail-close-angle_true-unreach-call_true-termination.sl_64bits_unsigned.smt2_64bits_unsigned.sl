(set-logic BV)

(synth-inv inv_fun ((buflim (_ BitVec 64))(buf (_ BitVec 64))(bufferlen (_ BitVec 64))(inlen (_ BitVec 64))(in (_ BitVec 64))))

(define-fun pre_fun ((buflim (_ BitVec 64)) (buf (_ BitVec 64)) (bufferlen (_ BitVec 64)) (inlen (_ BitVec 64)) (in (_ BitVec 64))) Bool
       ( and ( bvugt bufferlen #x0000000000000001 ) ( bvugt inlen #x0000000000000000 ) ( bvult bufferlen inlen ) ( = buf #x0000000000000000 ) ( = in #x0000000000000000 ) ( = buflim ( bvsub bufferlen #x0000000000000002 ) ) ))
(define-fun trans_fun ((buflim! (_ BitVec 64)) (buf! (_ BitVec 64)) (bufferlen! (_ BitVec 64)) (inlen! (_ BitVec 64)) (in! (_ BitVec 64)) (buflim (_ BitVec 64)) (buf (_ BitVec 64)) (bufferlen (_ BitVec 64)) (inlen (_ BitVec 64)) (in (_ BitVec 64))) Bool
       ( and ( not ( = buf buflim ) ) ( = buf! ( bvadd buf #x0000000000000001 ) ) ( = in! ( bvadd in #x0000000000000001 ) ) ( = inlen! inlen ) ( = bufferlen! bufferlen ) ( = buflim! buflim ) ))
(define-fun post_fun ((buflim (_ BitVec 64)) (buf (_ BitVec 64)) (bufferlen (_ BitVec 64)) (inlen (_ BitVec 64)) (in (_ BitVec 64))) Bool
       ( or ( not ( bvule bufferlen buf ) ) ( = buf buflim ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

