;; translated from ./bv/heapsort2.c.vmt
;; original benchmark available at: https://es-static.fbk.eu/people/griggio/ic3ia/index.html
;; author: Alberto Griggio <griggio@fbk.eu>
(set-logic HORN)
(declare-fun state (Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|n__2$main| (_ BitVec 32)) (|n__2$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|l__4$main| (_ BitVec 32)) (|l__4$main.next| (_ BitVec 32)) (|j__10$main.next| (_ BitVec 32)) (|j__10$main| (_ BitVec 32)) (|r__6$main| (_ BitVec 32)) (|r__6$main.next| (_ BitVec 32)) (|r__6$main.SSA.1.ssa| (_ BitVec 32)) (|l__4$main.SSA.1.ssa| (_ BitVec 32)) (|__NONDET_INLINE_INIT__3__7$main#0| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool)) (=> (let ((.def_15 (not .PC.2)))
(let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_16 (and .def_13 .def_15)))
.def_16))))) (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |j__10$main| |r__6$main| |l__4$main| |n__2$main|))))
(assert (forall ((|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|n__2$main| (_ BitVec 32)) (|n__2$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|l__4$main| (_ BitVec 32)) (|l__4$main.next| (_ BitVec 32)) (|j__10$main.next| (_ BitVec 32)) (|j__10$main| (_ BitVec 32)) (|r__6$main| (_ BitVec 32)) (|r__6$main.next| (_ BitVec 32)) (|r__6$main.SSA.1.ssa| (_ BitVec 32)) (|l__4$main.SSA.1.ssa| (_ BitVec 32)) (|__NONDET_INLINE_INIT__3__7$main#0| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool)) (=> (and (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |j__10$main| |r__6$main| |l__4$main| |n__2$main|) (let ((.def_12 (not .PC.1)))
(let ((.def_68 (and .PC.0 .def_12)))
(let ((.def_146 (and .PC.2 .def_68)))
(let ((.def_62 (not .PC.1.next)))
(let ((.def_64 (and .def_62 .PC.0.next)))
(let ((.def_142 (and .PC.2.next .def_64)))
(let ((.def_147 (and .def_142 .def_146)))
(let ((.def_78 (= n__2$main.next n__2$main)))
(let ((.def_53 (= __RET__$main __RET__$main.next)))
(let ((.def_138 (and .def_53 .def_78)))
(let ((.def_80 (= l__4$main.next l__4$main)))
(let ((.def_139 (and .def_80 .def_138)))
(let ((.def_57 (= j__10$main j__10$main.next)))
(let ((.def_140 (and .def_57 .def_139)))
(let ((.def_82 (= r__6$main.next r__6$main)))
(let ((.def_141 (and .def_82 .def_140)))
(let ((.def_143 (and .def_141 .def_142)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_137 (and .def_13 .PC.2)))
(let ((.def_144 (and .def_137 .def_143)))
(let ((.def_90 (bvslt r__6$main j__10$main)))
(let ((.def_128 (not .def_90)))
(let ((.def_126 (bvshl j__10$main (_ bv1 32))))
(let ((.def_127 (= j__10$main.next .def_126)))
(let ((.def_129 (and .def_127 .def_128)))
(let ((.def_130 (and .def_53 .def_129)))
(let ((.def_131 (and .def_78 .def_130)))
(let ((.def_132 (and .def_80 .def_131)))
(let ((.def_133 (and .def_82 .def_132)))
(let ((.def_84 (and .PC.1.next .PC.0.next)))
(let ((.def_60 (not .PC.2.next)))
(let ((.def_85 (and .def_60 .def_84)))
(let ((.def_134 (and .def_85 .def_133)))
(let ((.def_103 (and .PC.0 .PC.1)))
(let ((.def_15 (not .PC.2)))
(let ((.def_104 (and .def_15 .def_103)))
(let ((.def_135 (and .def_104 .def_134)))
(let ((.def_115 (bvadd (_ bv4294967295 32) r__6$main)))
(let ((.def_116 (= r__6$main.next .def_115)))
(let ((.def_89 (bvslt (_ bv1 32) l__4$main)))
(let ((.def_113 (not .def_89)))
(let ((.def_114 (and .def_90 .def_113)))
(let ((.def_117 (and .def_114 .def_116)))
(let ((.def_118 (and .def_80 .def_117)))
(let ((.def_109 (bvadd (_ bv4294967295 32) l__4$main)))
(let ((.def_110 (= l__4$main.next .def_109)))
(let ((.def_92 (bvslt n__2$main l__4$main)))
(let ((.def_107 (not .def_92)))
(let ((.def_91 (and .def_89 .def_90)))
(let ((.def_108 (and .def_91 .def_107)))
(let ((.def_111 (and .def_108 .def_110)))
(let ((.def_112 (and .def_82 .def_111)))
(let ((.def_119 (or .def_112 .def_118)))
(let ((.def_120 (and .def_53 .def_119)))
(let ((.def_121 (and .def_78 .def_120)))
(let ((.def_122 (and .def_57 .def_121)))
(let ((.def_65 (and .def_60 .def_64)))
(let ((.def_123 (and .def_65 .def_122)))
(let ((.def_124 (and .def_104 .def_123)))
(let ((.def_99 (not .PC.0.next)))
(let ((.def_100 (and .def_62 .def_99)))
(let ((.def_101 (and .PC.2.next .def_100)))
(let ((.def_93 (and .def_91 .def_92)))
(let ((.def_94 (and .def_53 .def_93)))
(let ((.def_95 (and .def_78 .def_94)))
(let ((.def_96 (and .def_80 .def_95)))
(let ((.def_97 (and .def_57 .def_96)))
(let ((.def_98 (and .def_82 .def_97)))
(let ((.def_102 (and .def_98 .def_101)))
(let ((.def_105 (and .def_102 .def_104)))
(let ((.def_73 (bvshl l__4$main (_ bv1 32))))
(let ((.def_74 (= j__10$main.next .def_73)))
(let ((.def_71 (bvslt (_ bv1 32) r__6$main)))
(let ((.def_75 (and .def_71 .def_74)))
(let ((.def_76 (and .def_53 .def_75)))
(let ((.def_79 (and .def_76 .def_78)))
(let ((.def_81 (and .def_79 .def_80)))
(let ((.def_83 (and .def_81 .def_82)))
(let ((.def_86 (and .def_83 .def_85)))
(let ((.def_69 (and .def_15 .def_68)))
(let ((.def_87 (and .def_69 .def_86)))
(let ((.def_46 (bvadd (_ bv4294967295 32) r__6$main.SSA.1.ssa)))
(let ((.def_47 (= r__6$main.next .def_46)))
(let ((.def_35 (bvslt (_ bv1 32) l__4$main.SSA.1.ssa)))
(let ((.def_44 (not .def_35)))
(let ((.def_29 (bvsdiv n__2$main.next (_ bv2 32))))
(let ((.def_30 (bvadd (_ bv1 32) .def_29)))
(let ((.def_32 (= .def_30 l__4$main.SSA.1.ssa)))
(let ((.def_25 (bvslt n__2$main.next (_ bv1 32))))
(let ((.def_26 (not .def_25)))
(let ((.def_23 (= n__2$main.next |__NONDET_INLINE_INIT__3__7$main#0|)))
(let ((.def_27 (and .def_23 .def_26)))
(let ((.def_33 (and .def_27 .def_32)))
(let ((.def_21 (= r__6$main.SSA.1.ssa n__2$main.next)))
(let ((.def_34 (and .def_21 .def_33)))
(let ((.def_45 (and .def_34 .def_44)))
(let ((.def_48 (and .def_45 .def_47)))
(let ((.def_43 (= l__4$main.SSA.1.ssa l__4$main.next)))
(let ((.def_49 (and .def_43 .def_48)))
(let ((.def_38 (bvadd (_ bv4294967295 32) l__4$main.SSA.1.ssa)))
(let ((.def_40 (= .def_38 l__4$main.next)))
(let ((.def_36 (and .def_34 .def_35)))
(let ((.def_41 (and .def_36 .def_40)))
(let ((.def_19 (= r__6$main.next r__6$main.SSA.1.ssa)))
(let ((.def_42 (and .def_19 .def_41)))
(let ((.def_50 (or .def_42 .def_49)))
(let ((.def_54 (and .def_50 .def_53)))
(let ((.def_58 (and .def_54 .def_57)))
(let ((.def_66 (and .def_58 .def_65)))
(let ((.def_16 (and .def_13 .def_15)))
(let ((.def_67 (and .def_16 .def_66)))
(let ((.def_88 (or .def_67 .def_87)))
(let ((.def_106 (or .def_88 .def_105)))
(let ((.def_125 (or .def_106 .def_124)))
(let ((.def_136 (or .def_125 .def_135)))
(let ((.def_145 (or .def_136 .def_144)))
(let ((.def_148 (or .def_145 .def_147)))
.def_148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (state |.PC.0.next| |.PC.1.next| |.PC.2.next| |__RET__$main.next| |j__10$main.next| |r__6$main.next| |l__4$main.next| |n__2$main.next|))))
(assert (forall ((|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|n__2$main| (_ BitVec 32)) (|n__2$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|l__4$main| (_ BitVec 32)) (|l__4$main.next| (_ BitVec 32)) (|j__10$main.next| (_ BitVec 32)) (|j__10$main| (_ BitVec 32)) (|r__6$main| (_ BitVec 32)) (|r__6$main.next| (_ BitVec 32)) (|r__6$main.SSA.1.ssa| (_ BitVec 32)) (|l__4$main.SSA.1.ssa| (_ BitVec 32)) (|__NONDET_INLINE_INIT__3__7$main#0| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool)) (=> (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |j__10$main| |r__6$main| |l__4$main| |n__2$main|) (let ((.def_12 (not .PC.1)))
(let ((.def_68 (and .PC.0 .def_12)))
(let ((.def_146 (and .PC.2 .def_68)))
(let ((.def_149 (not .def_146)))
.def_149)))))))
(check-sat)
