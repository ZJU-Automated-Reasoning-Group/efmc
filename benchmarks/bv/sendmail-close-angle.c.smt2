;; translated from ./bv/sendmail-close-angle.c.vmt
;; original benchmark available at: https://es-static.fbk.eu/people/griggio/ic3ia/index.html
;; author: Alberto Griggio <griggio@fbk.eu>
(set-logic HORN)
(declare-fun state (Bool Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((|.PC.2.next| Bool) (|.PC.1.next| Bool) (|.PC.3.next| Bool) (|buf__10$main| (_ BitVec 32)) (|buf__10$main.next| (_ BitVec 32)) (|__BLAST_NONDET__2$main| (_ BitVec 32)) (|__BLAST_NONDET__2$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|in__4$main| (_ BitVec 32)) (|in__4$main.next| (_ BitVec 32)) (|buflim__12$main| (_ BitVec 32)) (|buflim__12$main.next| (_ BitVec 32)) (|inlen__6$main| (_ BitVec 32)) (|inlen__6$main.next| (_ BitVec 32)) (|bufferlen__8$main| (_ BitVec 32)) (|bufferlen__8$main.next| (_ BitVec 32)) (|__NONDET_INLINE_INIT__9__11$main#2| (_ BitVec 32)) (|__NONDET_INLINE_INIT__7__10$main#1| (_ BitVec 32)) (|__NONDET_INLINE_INIT__3__8$main#0| (_ BitVec 32)) (|.PC.3| Bool) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool) (|.PC.0.next| Bool)) (=> (let ((.def_18 (not .PC.3)))
(let ((.def_15 (not .PC.2)))
(let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_16 (and .def_13 .def_15)))
(let ((.def_19 (and .def_16 .def_18)))
.def_19))))))) (state |.PC.0| |.PC.1| |.PC.2| |.PC.3| |__RET__$main| |buflim__12$main| |buf__10$main| |__BLAST_NONDET__2$main| |in__4$main| |inlen__6$main| |bufferlen__8$main|))))
(assert (forall ((|.PC.2.next| Bool) (|.PC.1.next| Bool) (|.PC.3.next| Bool) (|buf__10$main| (_ BitVec 32)) (|buf__10$main.next| (_ BitVec 32)) (|__BLAST_NONDET__2$main| (_ BitVec 32)) (|__BLAST_NONDET__2$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|in__4$main| (_ BitVec 32)) (|in__4$main.next| (_ BitVec 32)) (|buflim__12$main| (_ BitVec 32)) (|buflim__12$main.next| (_ BitVec 32)) (|inlen__6$main| (_ BitVec 32)) (|inlen__6$main.next| (_ BitVec 32)) (|bufferlen__8$main| (_ BitVec 32)) (|bufferlen__8$main.next| (_ BitVec 32)) (|__NONDET_INLINE_INIT__9__11$main#2| (_ BitVec 32)) (|__NONDET_INLINE_INIT__7__10$main#1| (_ BitVec 32)) (|__NONDET_INLINE_INIT__3__8$main#0| (_ BitVec 32)) (|.PC.3| Bool) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool) (|.PC.0.next| Bool)) (=> (and (state |.PC.0| |.PC.1| |.PC.2| |.PC.3| |__RET__$main| |buflim__12$main| |buf__10$main| |__BLAST_NONDET__2$main| |in__4$main| |inlen__6$main| |bufferlen__8$main|) (let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_254 (and .def_13 .PC.2)))
(let ((.def_266 (and .PC.3 .def_254)))
(let ((.def_93 (not .PC.0.next)))
(let ((.def_59 (not .PC.1.next)))
(let ((.def_136 (and .def_59 .def_93)))
(let ((.def_137 (and .PC.2.next .def_136)))
(let ((.def_233 (and .PC.3.next .def_137)))
(let ((.def_267 (and .def_233 .def_266)))
(let ((.def_245 (and .def_10 .PC.1)))
(let ((.def_15 (not .PC.2)))
(let ((.def_262 (and .def_15 .def_245)))
(let ((.def_18 (not .PC.3)))
(let ((.def_263 (and .def_18 .def_262)))
(let ((.def_79 (= buf__10$main.next buf__10$main)))
(let ((.def_77 (= __BLAST_NONDET__2$main.next __BLAST_NONDET__2$main)))
(let ((.def_227 (and .def_77 .def_79)))
(let ((.def_52 (= __RET__$main __RET__$main.next)))
(let ((.def_228 (and .def_52 .def_227)))
(let ((.def_83 (= in__4$main.next in__4$main)))
(let ((.def_229 (and .def_83 .def_228)))
(let ((.def_85 (= buflim__12$main.next buflim__12$main)))
(let ((.def_230 (and .def_85 .def_229)))
(let ((.def_88 (= inlen__6$main.next inlen__6$main)))
(let ((.def_231 (and .def_88 .def_230)))
(let ((.def_91 (= bufferlen__8$main.next bufferlen__8$main)))
(let ((.def_232 (and .def_91 .def_231)))
(let ((.def_234 (and .def_232 .def_233)))
(let ((.def_264 (and .def_234 .def_263)))
(let ((.def_240 (and .PC.0 .PC.1)))
(let ((.def_258 (and .def_15 .def_240)))
(let ((.def_259 (and .def_18 .def_258)))
(let ((.def_260 (and .def_234 .def_259)))
(let ((.def_255 (and .def_18 .def_254)))
(let ((.def_256 (and .def_234 .def_255)))
(let ((.def_98 (and .PC.0 .def_12)))
(let ((.def_250 (and .PC.2 .def_98)))
(let ((.def_251 (and .def_18 .def_250)))
(let ((.def_252 (and .def_234 .def_251)))
(let ((.def_246 (and .PC.2 .def_245)))
(let ((.def_247 (and .def_18 .def_246)))
(let ((.def_248 (and .def_234 .def_247)))
(let ((.def_241 (and .PC.2 .def_240)))
(let ((.def_242 (and .def_18 .def_241)))
(let ((.def_243 (and .def_234 .def_242)))
(let ((.def_16 (and .def_13 .def_15)))
(let ((.def_237 (and .def_16 .PC.3)))
(let ((.def_238 (and .def_234 .def_237)))
(let ((.def_99 (and .def_15 .def_98)))
(let ((.def_226 (and .PC.3 .def_99)))
(let ((.def_235 (and .def_226 .def_234)))
(let ((.def_61 (and .def_59 .PC.0.next)))
(let ((.def_57 (not .PC.2.next)))
(let ((.def_62 (and .def_57 .def_61)))
(let ((.def_222 (and .PC.3.next .def_62)))
(let ((.def_197 ((_ extract 31 31) buf__10$main.next)))
(let ((.def_198 (= .def_197 (_ bv1 1))))
(let ((.def_213 (not .def_198)))
(let ((.def_71 (= __BLAST_NONDET__2$main (_ bv0 32))))
(let ((.def_72 (not .def_71)))
(let ((.def_68 (= buflim__12$main buf__10$main)))
(let ((.def_166 (and .def_68 .def_72)))
(let ((.def_167 (or .def_71 .def_166)))
(let ((.def_74 ((_ extract 31 31) buf__10$main)))
(let ((.def_75 (= .def_74 (_ bv1 1))))
(let ((.def_103 (not .def_75)))
(let ((.def_181 (and .def_103 .def_167)))
(let ((.def_105 (bvslt buf__10$main bufferlen__8$main)))
(let ((.def_195 (and .def_105 .def_181)))
(let ((.def_122 (bvadd (_ bv1 32) buf__10$main)))
(let ((.def_123 (= buf__10$main.next .def_122)))
(let ((.def_196 (and .def_123 .def_195)))
(let ((.def_214 (and .def_196 .def_213)))
(let ((.def_211 (bvslt buf__10$main.next bufferlen__8$main)))
(let ((.def_212 (not .def_211)))
(let ((.def_215 (and .def_212 .def_214)))
(let ((.def_216 (and .def_77 .def_215)))
(let ((.def_217 (and .def_52 .def_216)))
(let ((.def_218 (and .def_83 .def_217)))
(let ((.def_219 (and .def_85 .def_218)))
(let ((.def_220 (and .def_88 .def_219)))
(let ((.def_221 (and .def_91 .def_220)))
(let ((.def_223 (and .def_221 .def_222)))
(let ((.def_100 (and .def_18 .def_99)))
(let ((.def_224 (and .def_100 .def_223)))
(let ((.def_206 (and .def_57 .def_136)))
(let ((.def_207 (and .PC.3.next .def_206)))
(let ((.def_199 (and .def_196 .def_198)))
(let ((.def_200 (and .def_77 .def_199)))
(let ((.def_201 (and .def_52 .def_200)))
(let ((.def_202 (and .def_83 .def_201)))
(let ((.def_203 (and .def_85 .def_202)))
(let ((.def_204 (and .def_88 .def_203)))
(let ((.def_205 (and .def_91 .def_204)))
(let ((.def_208 (and .def_205 .def_207)))
(let ((.def_209 (and .def_100 .def_208)))
(let ((.def_115 (and .PC.1.next .PC.0.next)))
(let ((.def_190 (and .PC.2.next .def_115)))
(let ((.def_55 (not .PC.3.next)))
(let ((.def_191 (and .def_55 .def_190)))
(let ((.def_106 (not .def_105)))
(let ((.def_182 (and .def_106 .def_181)))
(let ((.def_183 (and .def_77 .def_182)))
(let ((.def_184 (and .def_79 .def_183)))
(let ((.def_185 (and .def_52 .def_184)))
(let ((.def_186 (and .def_83 .def_185)))
(let ((.def_187 (and .def_85 .def_186)))
(let ((.def_188 (and .def_88 .def_187)))
(let ((.def_189 (and .def_91 .def_188)))
(let ((.def_192 (and .def_189 .def_191)))
(let ((.def_193 (and .def_100 .def_192)))
(let ((.def_94 (and .PC.1.next .def_93)))
(let ((.def_176 (and .PC.2.next .def_94)))
(let ((.def_177 (and .def_55 .def_176)))
(let ((.def_168 (and .def_75 .def_167)))
(let ((.def_169 (and .def_77 .def_168)))
(let ((.def_170 (and .def_79 .def_169)))
(let ((.def_171 (and .def_52 .def_170)))
(let ((.def_172 (and .def_83 .def_171)))
(let ((.def_173 (and .def_85 .def_172)))
(let ((.def_174 (and .def_88 .def_173)))
(let ((.def_175 (and .def_91 .def_174)))
(let ((.def_178 (and .def_175 .def_177)))
(let ((.def_179 (and .def_100 .def_178)))
(let ((.def_128 ((_ extract 31 31) in__4$main.next)))
(let ((.def_129 (= .def_128 (_ bv1 1))))
(let ((.def_144 (not .def_129)))
(let ((.def_125 (bvadd (_ bv1 32) in__4$main)))
(let ((.def_126 (= in__4$main.next .def_125)))
(let ((.def_69 (not .def_68)))
(let ((.def_73 (and .def_69 .def_72)))
(let ((.def_104 (and .def_73 .def_103)))
(let ((.def_121 (and .def_104 .def_105)))
(let ((.def_124 (and .def_121 .def_123)))
(let ((.def_127 (and .def_124 .def_126)))
(let ((.def_145 (and .def_127 .def_144)))
(let ((.def_142 (bvslt in__4$main.next inlen__6$main)))
(let ((.def_157 (and .def_142 .def_145)))
(let ((.def_158 (and .def_77 .def_157)))
(let ((.def_159 (and .def_52 .def_158)))
(let ((.def_160 (and .def_85 .def_159)))
(let ((.def_161 (and .def_88 .def_160)))
(let ((.def_162 (and .def_91 .def_161)))
(let ((.def_63 (and .def_55 .def_62)))
(let ((.def_163 (and .def_63 .def_162)))
(let ((.def_164 (and .def_100 .def_163)))
(let ((.def_152 (and .PC.2.next .def_61)))
(let ((.def_153 (and .def_55 .def_152)))
(let ((.def_143 (not .def_142)))
(let ((.def_146 (and .def_143 .def_145)))
(let ((.def_147 (and .def_77 .def_146)))
(let ((.def_148 (and .def_52 .def_147)))
(let ((.def_149 (and .def_85 .def_148)))
(let ((.def_150 (and .def_88 .def_149)))
(let ((.def_151 (and .def_91 .def_150)))
(let ((.def_154 (and .def_151 .def_153)))
(let ((.def_155 (and .def_100 .def_154)))
(let ((.def_138 (and .def_55 .def_137)))
(let ((.def_130 (and .def_127 .def_129)))
(let ((.def_131 (and .def_77 .def_130)))
(let ((.def_132 (and .def_52 .def_131)))
(let ((.def_133 (and .def_85 .def_132)))
(let ((.def_134 (and .def_88 .def_133)))
(let ((.def_135 (and .def_91 .def_134)))
(let ((.def_139 (and .def_135 .def_138)))
(let ((.def_140 (and .def_100 .def_139)))
(let ((.def_116 (and .def_57 .def_115)))
(let ((.def_117 (and .def_55 .def_116)))
(let ((.def_107 (and .def_104 .def_106)))
(let ((.def_108 (and .def_77 .def_107)))
(let ((.def_109 (and .def_79 .def_108)))
(let ((.def_110 (and .def_52 .def_109)))
(let ((.def_111 (and .def_83 .def_110)))
(let ((.def_112 (and .def_85 .def_111)))
(let ((.def_113 (and .def_88 .def_112)))
(let ((.def_114 (and .def_91 .def_113)))
(let ((.def_118 (and .def_114 .def_117)))
(let ((.def_119 (and .def_100 .def_118)))
(let ((.def_95 (and .def_57 .def_94)))
(let ((.def_96 (and .def_55 .def_95)))
(let ((.def_76 (and .def_73 .def_75)))
(let ((.def_78 (and .def_76 .def_77)))
(let ((.def_80 (and .def_78 .def_79)))
(let ((.def_81 (and .def_52 .def_80)))
(let ((.def_84 (and .def_81 .def_83)))
(let ((.def_86 (and .def_84 .def_85)))
(let ((.def_89 (and .def_86 .def_88)))
(let ((.def_92 (and .def_89 .def_91)))
(let ((.def_97 (and .def_92 .def_96)))
(let ((.def_101 (and .def_97 .def_100)))
(let ((.def_46 (bvadd (_ bv4294967294 32) bufferlen__8$main.next)))
(let ((.def_48 (= .def_46 buflim__12$main.next)))
(let ((.def_43 (= in__4$main.next (_ bv0 32))))
(let ((.def_40 (= buf__10$main.next (_ bv0 32))))
(let ((.def_36 (bvslt (_ bv0 32) inlen__6$main.next)))
(let ((.def_33 (bvslt (_ bv1 32) bufferlen__8$main.next)))
(let ((.def_30 (= bufferlen__8$main.next |__NONDET_INLINE_INIT__9__11$main#2|)))
(let ((.def_27 (= inlen__6$main.next |__NONDET_INLINE_INIT__7__10$main#1|)))
(let ((.def_25 (= __BLAST_NONDET__2$main.next |__NONDET_INLINE_INIT__3__8$main#0|)))
(let ((.def_28 (and .def_25 .def_27)))
(let ((.def_31 (and .def_28 .def_30)))
(let ((.def_34 (and .def_31 .def_33)))
(let ((.def_37 (and .def_34 .def_36)))
(let ((.def_22 (bvslt bufferlen__8$main.next inlen__6$main.next)))
(let ((.def_38 (and .def_22 .def_37)))
(let ((.def_41 (and .def_38 .def_40)))
(let ((.def_44 (and .def_41 .def_43)))
(let ((.def_49 (and .def_44 .def_48)))
(let ((.def_53 (and .def_49 .def_52)))
(let ((.def_64 (and .def_53 .def_63)))
(let ((.def_19 (and .def_16 .def_18)))
(let ((.def_65 (and .def_19 .def_64)))
(let ((.def_102 (or .def_65 .def_101)))
(let ((.def_120 (or .def_102 .def_119)))
(let ((.def_141 (or .def_120 .def_140)))
(let ((.def_156 (or .def_141 .def_155)))
(let ((.def_165 (or .def_156 .def_164)))
(let ((.def_180 (or .def_165 .def_179)))
(let ((.def_194 (or .def_180 .def_193)))
(let ((.def_210 (or .def_194 .def_209)))
(let ((.def_225 (or .def_210 .def_224)))
(let ((.def_236 (or .def_225 .def_235)))
(let ((.def_239 (or .def_236 .def_238)))
(let ((.def_244 (or .def_239 .def_243)))
(let ((.def_249 (or .def_244 .def_248)))
(let ((.def_253 (or .def_249 .def_252)))
(let ((.def_257 (or .def_253 .def_256)))
(let ((.def_261 (or .def_257 .def_260)))
(let ((.def_265 (or .def_261 .def_264)))
(let ((.def_268 (or .def_265 .def_267)))
.def_268))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (state |.PC.0.next| |.PC.1.next| |.PC.2.next| |.PC.3.next| |__RET__$main.next| |buflim__12$main.next| |buf__10$main.next| |__BLAST_NONDET__2$main.next| |in__4$main.next| |inlen__6$main.next| |bufferlen__8$main.next|))))
(assert (forall ((|.PC.2.next| Bool) (|.PC.1.next| Bool) (|.PC.3.next| Bool) (|buf__10$main| (_ BitVec 32)) (|buf__10$main.next| (_ BitVec 32)) (|__BLAST_NONDET__2$main| (_ BitVec 32)) (|__BLAST_NONDET__2$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|in__4$main| (_ BitVec 32)) (|in__4$main.next| (_ BitVec 32)) (|buflim__12$main| (_ BitVec 32)) (|buflim__12$main.next| (_ BitVec 32)) (|inlen__6$main| (_ BitVec 32)) (|inlen__6$main.next| (_ BitVec 32)) (|bufferlen__8$main| (_ BitVec 32)) (|bufferlen__8$main.next| (_ BitVec 32)) (|__NONDET_INLINE_INIT__9__11$main#2| (_ BitVec 32)) (|__NONDET_INLINE_INIT__7__10$main#1| (_ BitVec 32)) (|__NONDET_INLINE_INIT__3__8$main#0| (_ BitVec 32)) (|.PC.3| Bool) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool) (|.PC.0.next| Bool)) (=> (state |.PC.0| |.PC.1| |.PC.2| |.PC.3| |__RET__$main| |buflim__12$main| |buf__10$main| |__BLAST_NONDET__2$main| |in__4$main| |inlen__6$main| |bufferlen__8$main|) (let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_254 (and .def_13 .PC.2)))
(let ((.def_266 (and .PC.3 .def_254)))
(let ((.def_269 (not .def_266)))
.def_269)))))))))
(check-sat)
