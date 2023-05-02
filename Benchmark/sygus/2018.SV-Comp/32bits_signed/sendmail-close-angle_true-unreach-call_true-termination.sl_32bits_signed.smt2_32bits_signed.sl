(set-logic BV)

(synth-inv inv_fun ((buflim (_ BitVec 32))(buf (_ BitVec 32))(bufferlen (_ BitVec 32))(inlen (_ BitVec 32))(in (_ BitVec 32))))

(define-fun pre_fun ((buflim (_ BitVec 32)) (buf (_ BitVec 32)) (bufferlen (_ BitVec 32)) (inlen (_ BitVec 32)) (in (_ BitVec 32))) Bool
       ( and ( bvsgt bufferlen #x00000001 ) ( bvsgt inlen #x00000000 ) ( bvslt bufferlen inlen ) ( = buf #x00000000 ) ( = in #x00000000 ) ( = buflim ( bvsub bufferlen #x00000002 ) ) ))
(define-fun trans_fun ((buflim! (_ BitVec 32)) (buf! (_ BitVec 32)) (bufferlen! (_ BitVec 32)) (inlen! (_ BitVec 32)) (in! (_ BitVec 32)) (buflim (_ BitVec 32)) (buf (_ BitVec 32)) (bufferlen (_ BitVec 32)) (inlen (_ BitVec 32)) (in (_ BitVec 32))) Bool
       ( and ( not ( = buf buflim ) ) ( = buf! ( bvadd buf #x00000001 ) ) ( = in! ( bvadd in #x00000001 ) ) ( = inlen! inlen ) ( = bufferlen! bufferlen ) ( = buflim! buflim ) ))
(define-fun post_fun ((buflim (_ BitVec 32)) (buf (_ BitVec 32)) (bufferlen (_ BitVec 32)) (inlen (_ BitVec 32)) (in (_ BitVec 32))) Bool
       ( or ( = buf buflim ) ( and ( bvsle #x00000000 buf ) ( not ( bvsle bufferlen buf ) ) ) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

