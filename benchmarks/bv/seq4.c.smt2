;; translated from ./bv/seq4.c.vmt
;; original benchmark available at: https://es-static.fbk.eu/people/griggio/ic3ia/index.html
;; author: Alberto Griggio <griggio@fbk.eu>
(set-logic HORN)
(declare-fun state (Bool Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((|.PC.1| Bool) (|.PC.0| Bool) (|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|.PC.3.next| Bool) (|j0__14$main| (_ BitVec 32)) (|j0__14$main.next| (_ BitVec 32)) (|n0__2$main| (_ BitVec 32)) (|k__8$main| (_ BitVec 32)) (|k__8$main.next| (_ BitVec 32)) (|n0__2$main.next| (_ BitVec 32)) (|i0__6$main| (_ BitVec 32)) (|i0__6$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|n1__4$main| (_ BitVec 32)) (|n1__4$main.next| (_ BitVec 32)) (|j1__12$main.next| (_ BitVec 32)) (|j1__12$main| (_ BitVec 32)) (|i1__10$main.next| (_ BitVec 32)) (|i1__10$main| (_ BitVec 32)) (|__NONDET_INLINE_INIT__5__10$main#1| (_ BitVec 32)) (|__NONDET_INLINE_INIT__3__9$main#0| (_ BitVec 32)) (|.PC.3| Bool) (|.PC.2| Bool)) (=> (let ((.def_18 (not .PC.3)))
(let ((.def_15 (not .PC.2)))
(let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_16 (and .def_13 .def_15)))
(let ((.def_19 (and .def_16 .def_18)))
.def_19))))))) (state |.PC.0| |.PC.1| |.PC.2| |.PC.3| |j0__14$main| |__RET__$main| |j1__12$main| |i1__10$main| |n0__2$main| |i0__6$main| |n1__4$main| |k__8$main|))))
(assert (forall ((|.PC.1| Bool) (|.PC.0| Bool) (|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|.PC.3.next| Bool) (|j0__14$main| (_ BitVec 32)) (|j0__14$main.next| (_ BitVec 32)) (|n0__2$main| (_ BitVec 32)) (|k__8$main| (_ BitVec 32)) (|k__8$main.next| (_ BitVec 32)) (|n0__2$main.next| (_ BitVec 32)) (|i0__6$main| (_ BitVec 32)) (|i0__6$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|n1__4$main| (_ BitVec 32)) (|n1__4$main.next| (_ BitVec 32)) (|j1__12$main.next| (_ BitVec 32)) (|j1__12$main| (_ BitVec 32)) (|i1__10$main.next| (_ BitVec 32)) (|i1__10$main| (_ BitVec 32)) (|__NONDET_INLINE_INIT__5__10$main#1| (_ BitVec 32)) (|__NONDET_INLINE_INIT__3__9$main#0| (_ BitVec 32)) (|.PC.3| Bool) (|.PC.2| Bool)) (=> (and (state |.PC.0| |.PC.1| |.PC.2| |.PC.3| |j0__14$main| |__RET__$main| |j1__12$main| |i1__10$main| |n0__2$main| |i0__6$main| |n1__4$main| |k__8$main|) (let ((.def_155 (and .PC.0 .PC.1)))
(let ((.def_223 (and .PC.2 .def_155)))
(let ((.def_18 (not .PC.3)))
(let ((.def_224 (and .def_18 .def_223)))
(let ((.def_118 (and .PC.1.next .PC.0.next)))
(let ((.def_202 (and .PC.2.next .def_118)))
(let ((.def_58 (not .PC.3.next)))
(let ((.def_203 (and .def_58 .def_202)))
(let ((.def_225 (and .def_203 .def_224)))
(let ((.def_210 (bvadd (_ bv1 32) j0__14$main)))
(let ((.def_211 (= j0__14$main.next .def_210)))
(let ((.def_209 (bvslt j0__14$main n0__2$main)))
(let ((.def_212 (and .def_209 .def_211)))
(let ((.def_181 (bvadd (_ bv4294967295 32) k__8$main)))
(let ((.def_182 (= k__8$main.next .def_181)))
(let ((.def_213 (and .def_182 .def_212)))
(let ((.def_68 (= n0__2$main.next n0__2$main)))
(let ((.def_214 (and .def_68 .def_213)))
(let ((.def_70 (= i0__6$main.next i0__6$main)))
(let ((.def_215 (and .def_70 .def_214)))
(let ((.def_40 (= __RET__$main __RET__$main.next)))
(let ((.def_216 (and .def_40 .def_215)))
(let ((.def_75 (= n1__4$main.next n1__4$main)))
(let ((.def_217 (and .def_75 .def_216)))
(let ((.def_44 (= j1__12$main j1__12$main.next)))
(let ((.def_218 (and .def_44 .def_217)))
(let ((.def_48 (= i1__10$main i1__10$main.next)))
(let ((.def_219 (and .def_48 .def_218)))
(let ((.def_81 (not .PC.0.next)))
(let ((.def_51 (not .PC.1.next)))
(let ((.def_151 (and .def_51 .def_81)))
(let ((.def_152 (and .PC.2.next .def_151)))
(let ((.def_153 (and .def_58 .def_152)))
(let ((.def_220 (and .def_153 .def_219)))
(let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_207 (and .def_13 .PC.2)))
(let ((.def_208 (and .def_18 .def_207)))
(let ((.def_221 (and .def_208 .def_220)))
(let ((.def_195 (and .def_68 .def_70)))
(let ((.def_36 (= j0__14$main j0__14$main.next)))
(let ((.def_196 (and .def_36 .def_195)))
(let ((.def_197 (and .def_40 .def_196)))
(let ((.def_198 (and .def_75 .def_197)))
(let ((.def_199 (and .def_44 .def_198)))
(let ((.def_200 (and .def_48 .def_199)))
(let ((.def_79 (= k__8$main.next k__8$main)))
(let ((.def_201 (and .def_79 .def_200)))
(let ((.def_204 (and .def_201 .def_203)))
(let ((.def_122 (and .def_10 .PC.1)))
(let ((.def_193 (and .PC.2 .def_122)))
(let ((.def_194 (and .def_18 .def_193)))
(let ((.def_205 (and .def_194 .def_204)))
(let ((.def_177 (bvadd (_ bv1 32) j1__12$main)))
(let ((.def_178 (= j1__12$main.next .def_177)))
(let ((.def_160 (bvslt (_ bv0 32) k__8$main)))
(let ((.def_140 (bvslt j1__12$main n1__4$main)))
(let ((.def_176 (and .def_140 .def_160)))
(let ((.def_179 (and .def_176 .def_178)))
(let ((.def_183 (and .def_179 .def_182)))
(let ((.def_184 (and .def_68 .def_183)))
(let ((.def_185 (and .def_70 .def_184)))
(let ((.def_186 (and .def_36 .def_185)))
(let ((.def_187 (and .def_40 .def_186)))
(let ((.def_188 (and .def_75 .def_187)))
(let ((.def_189 (and .def_48 .def_188)))
(let ((.def_55 (not .PC.2.next)))
(let ((.def_119 (and .def_55 .def_118)))
(let ((.def_120 (and .def_58 .def_119)))
(let ((.def_190 (and .def_120 .def_189)))
(let ((.def_15 (not .PC.2)))
(let ((.def_156 (and .def_15 .def_155)))
(let ((.def_157 (and .def_18 .def_156)))
(let ((.def_191 (and .def_157 .def_190)))
(let ((.def_82 (and .PC.1.next .def_81)))
(let ((.def_171 (and .PC.2.next .def_82)))
(let ((.def_172 (and .def_58 .def_171)))
(let ((.def_161 (not .def_160)))
(let ((.def_162 (and .def_140 .def_161)))
(let ((.def_163 (and .def_68 .def_162)))
(let ((.def_164 (and .def_70 .def_163)))
(let ((.def_165 (and .def_36 .def_164)))
(let ((.def_166 (and .def_40 .def_165)))
(let ((.def_167 (and .def_75 .def_166)))
(let ((.def_168 (and .def_44 .def_167)))
(let ((.def_169 (and .def_48 .def_168)))
(let ((.def_170 (and .def_79 .def_169)))
(let ((.def_173 (and .def_170 .def_172)))
(let ((.def_174 (and .def_157 .def_173)))
(let ((.def_142 (= j0__14$main.next (_ bv0 32))))
(let ((.def_141 (not .def_140)))
(let ((.def_143 (and .def_141 .def_142)))
(let ((.def_144 (and .def_68 .def_143)))
(let ((.def_145 (and .def_70 .def_144)))
(let ((.def_146 (and .def_40 .def_145)))
(let ((.def_147 (and .def_75 .def_146)))
(let ((.def_148 (and .def_44 .def_147)))
(let ((.def_149 (and .def_48 .def_148)))
(let ((.def_150 (and .def_79 .def_149)))
(let ((.def_154 (and .def_150 .def_153)))
(let ((.def_158 (and .def_154 .def_157)))
(let ((.def_127 (bvadd (_ bv1 32) i1__10$main)))
(let ((.def_128 (= i1__10$main.next .def_127)))
(let ((.def_107 (bvslt i1__10$main n1__4$main)))
(let ((.def_129 (and .def_107 .def_128)))
(let ((.def_95 (bvadd (_ bv1 32) k__8$main)))
(let ((.def_96 (= k__8$main.next .def_95)))
(let ((.def_130 (and .def_96 .def_129)))
(let ((.def_131 (and .def_68 .def_130)))
(let ((.def_132 (and .def_70 .def_131)))
(let ((.def_133 (and .def_36 .def_132)))
(let ((.def_134 (and .def_40 .def_133)))
(let ((.def_135 (and .def_75 .def_134)))
(let ((.def_136 (and .def_44 .def_135)))
(let ((.def_83 (and .def_55 .def_82)))
(let ((.def_84 (and .def_58 .def_83)))
(let ((.def_137 (and .def_84 .def_136)))
(let ((.def_123 (and .def_15 .def_122)))
(let ((.def_124 (and .def_18 .def_123)))
(let ((.def_138 (and .def_124 .def_137)))
(let ((.def_109 (= j1__12$main.next (_ bv0 32))))
(let ((.def_108 (not .def_107)))
(let ((.def_110 (and .def_108 .def_109)))
(let ((.def_111 (and .def_68 .def_110)))
(let ((.def_112 (and .def_70 .def_111)))
(let ((.def_113 (and .def_36 .def_112)))
(let ((.def_114 (and .def_40 .def_113)))
(let ((.def_115 (and .def_75 .def_114)))
(let ((.def_116 (and .def_48 .def_115)))
(let ((.def_117 (and .def_79 .def_116)))
(let ((.def_121 (and .def_117 .def_120)))
(let ((.def_125 (and .def_121 .def_124)))
(let ((.def_92 (bvadd (_ bv1 32) i0__6$main)))
(let ((.def_93 (= i0__6$main.next .def_92)))
(let ((.def_64 (bvslt i0__6$main n0__2$main)))
(let ((.def_94 (and .def_64 .def_93)))
(let ((.def_97 (and .def_94 .def_96)))
(let ((.def_98 (and .def_68 .def_97)))
(let ((.def_99 (and .def_36 .def_98)))
(let ((.def_100 (and .def_40 .def_99)))
(let ((.def_101 (and .def_75 .def_100)))
(let ((.def_102 (and .def_44 .def_101)))
(let ((.def_103 (and .def_48 .def_102)))
(let ((.def_53 (and .def_51 .PC.0.next)))
(let ((.def_56 (and .def_53 .def_55)))
(let ((.def_59 (and .def_56 .def_58)))
(let ((.def_104 (and .def_59 .def_103)))
(let ((.def_86 (and .PC.0 .def_12)))
(let ((.def_87 (and .def_15 .def_86)))
(let ((.def_88 (and .def_18 .def_87)))
(let ((.def_105 (and .def_88 .def_104)))
(let ((.def_66 (= i1__10$main.next (_ bv0 32))))
(let ((.def_65 (not .def_64)))
(let ((.def_67 (and .def_65 .def_66)))
(let ((.def_69 (and .def_67 .def_68)))
(let ((.def_71 (and .def_69 .def_70)))
(let ((.def_72 (and .def_36 .def_71)))
(let ((.def_73 (and .def_40 .def_72)))
(let ((.def_76 (and .def_73 .def_75)))
(let ((.def_77 (and .def_44 .def_76)))
(let ((.def_80 (and .def_77 .def_79)))
(let ((.def_85 (and .def_80 .def_84)))
(let ((.def_89 (and .def_85 .def_88)))
(let ((.def_32 (= k__8$main.next (_ bv0 32))))
(let ((.def_29 (= i0__6$main.next (_ bv0 32))))
(let ((.def_25 (= n1__4$main.next |__NONDET_INLINE_INIT__5__10$main#1|)))
(let ((.def_22 (= n0__2$main.next |__NONDET_INLINE_INIT__3__9$main#0|)))
(let ((.def_26 (and .def_22 .def_25)))
(let ((.def_30 (and .def_26 .def_29)))
(let ((.def_33 (and .def_30 .def_32)))
(let ((.def_37 (and .def_33 .def_36)))
(let ((.def_41 (and .def_37 .def_40)))
(let ((.def_45 (and .def_41 .def_44)))
(let ((.def_49 (and .def_45 .def_48)))
(let ((.def_60 (and .def_49 .def_59)))
(let ((.def_16 (and .def_13 .def_15)))
(let ((.def_19 (and .def_16 .def_18)))
(let ((.def_61 (and .def_19 .def_60)))
(let ((.def_90 (or .def_61 .def_89)))
(let ((.def_106 (or .def_90 .def_105)))
(let ((.def_126 (or .def_106 .def_125)))
(let ((.def_139 (or .def_126 .def_138)))
(let ((.def_159 (or .def_139 .def_158)))
(let ((.def_175 (or .def_159 .def_174)))
(let ((.def_192 (or .def_175 .def_191)))
(let ((.def_206 (or .def_192 .def_205)))
(let ((.def_222 (or .def_206 .def_221)))
(let ((.def_226 (or .def_222 .def_225)))
.def_226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (state |.PC.0.next| |.PC.1.next| |.PC.2.next| |.PC.3.next| |j0__14$main.next| |__RET__$main.next| |j1__12$main.next| |i1__10$main.next| |n0__2$main.next| |i0__6$main.next| |n1__4$main.next| |k__8$main.next|))))
(assert (forall ((|.PC.1| Bool) (|.PC.0| Bool) (|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|.PC.3.next| Bool) (|j0__14$main| (_ BitVec 32)) (|j0__14$main.next| (_ BitVec 32)) (|n0__2$main| (_ BitVec 32)) (|k__8$main| (_ BitVec 32)) (|k__8$main.next| (_ BitVec 32)) (|n0__2$main.next| (_ BitVec 32)) (|i0__6$main| (_ BitVec 32)) (|i0__6$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|n1__4$main| (_ BitVec 32)) (|n1__4$main.next| (_ BitVec 32)) (|j1__12$main.next| (_ BitVec 32)) (|j1__12$main| (_ BitVec 32)) (|i1__10$main.next| (_ BitVec 32)) (|i1__10$main| (_ BitVec 32)) (|__NONDET_INLINE_INIT__5__10$main#1| (_ BitVec 32)) (|__NONDET_INLINE_INIT__3__9$main#0| (_ BitVec 32)) (|.PC.3| Bool) (|.PC.2| Bool)) (=> (state |.PC.0| |.PC.1| |.PC.2| |.PC.3| |j0__14$main| |__RET__$main| |j1__12$main| |i1__10$main| |n0__2$main| |i0__6$main| |n1__4$main| |k__8$main|) (let ((.def_155 (and .PC.0 .PC.1)))
(let ((.def_223 (and .PC.2 .def_155)))
(let ((.def_18 (not .PC.3)))
(let ((.def_224 (and .def_18 .def_223)))
(let ((.def_227 (not .def_224)))
.def_227))))))))
(check-sat)
