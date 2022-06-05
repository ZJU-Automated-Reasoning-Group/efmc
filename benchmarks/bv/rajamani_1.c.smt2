;; translated from ./bv/rajamani_1.c.vmt
;; original benchmark available at: https://es-static.fbk.eu/people/griggio/ic3ia/index.html
;; author: Alberto Griggio <griggio@fbk.eu>
(set-logic HORN)
(declare-fun state (Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|z__6$main| (_ BitVec 32)) (|z__6$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|x__2$main| (_ BitVec 32)) (|x__2$main.next| (_ BitVec 32)) (|w__8$main| (_ BitVec 32)) (|w__8$main.next| (_ BitVec 32)) (|y__4$main| (_ BitVec 32)) (|y__4$main.next| (_ BitVec 32)) (|__NONDET__11$main#2| (_ BitVec 32)) (|__NONDET__12$main#3| (_ BitVec 32)) (|__NONDET__13$main#4| (_ BitVec 32)) (|__NONDET__11$main#0| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool)) (=> (let ((.def_15 (not .PC.2)))
(let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_16 (and .def_13 .def_15)))
.def_16))))) (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |x__2$main| |y__4$main| |z__6$main| |w__8$main|))))
(assert (forall ((|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|z__6$main| (_ BitVec 32)) (|z__6$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|x__2$main| (_ BitVec 32)) (|x__2$main.next| (_ BitVec 32)) (|w__8$main| (_ BitVec 32)) (|w__8$main.next| (_ BitVec 32)) (|y__4$main| (_ BitVec 32)) (|y__4$main.next| (_ BitVec 32)) (|__NONDET__11$main#2| (_ BitVec 32)) (|__NONDET__12$main#3| (_ BitVec 32)) (|__NONDET__13$main#4| (_ BitVec 32)) (|__NONDET__11$main#0| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool)) (=> (and (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |x__2$main| |y__4$main| |z__6$main| |w__8$main|) (let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_145 (and .def_13 .PC.2)))
(let ((.def_64 (not .PC.0.next)))
(let ((.def_36 (not .PC.1.next)))
(let ((.def_140 (and .def_36 .def_64)))
(let ((.def_141 (and .PC.2.next .def_140)))
(let ((.def_146 (and .def_141 .def_145)))
(let ((.def_55 (= z__6$main.next z__6$main)))
(let ((.def_31 (= __RET__$main __RET__$main.next)))
(let ((.def_136 (and .def_31 .def_55)))
(let ((.def_57 (= x__2$main.next x__2$main)))
(let ((.def_137 (and .def_57 .def_136)))
(let ((.def_60 (= w__8$main.next w__8$main)))
(let ((.def_138 (and .def_60 .def_137)))
(let ((.def_62 (= y__4$main.next y__4$main)))
(let ((.def_139 (and .def_62 .def_138)))
(let ((.def_142 (and .def_139 .def_141)))
(let ((.def_134 (and .def_10 .PC.1)))
(let ((.def_15 (not .PC.2)))
(let ((.def_135 (and .def_15 .def_134)))
(let ((.def_143 (and .def_135 .def_142)))
(let ((.def_127 (bvadd (_ bv10 32) z__6$main)))
(let ((.def_128 (= z__6$main.next .def_127)))
(let ((.def_124 (bvadd (_ bv1 32) w__8$main)))
(let ((.def_125 (= w__8$main.next .def_124)))
(let ((.def_76 (= |__NONDET__11$main#2| (_ bv0 32))))
(let ((.def_77 (not .def_76)))
(let ((.def_73 (= |__NONDET__12$main#3| (_ bv0 32))))
(let ((.def_90 (and .def_73 .def_77)))
(let ((.def_88 (= |__NONDET__13$main#4| (_ bv0 32))))
(let ((.def_111 (and .def_88 .def_90)))
(let ((.def_107 (bvmul (_ bv10 32) w__8$main)))
(let ((.def_108 (bvadd (_ bv1 32) .def_107)))
(let ((.def_109 (bvslt y__4$main .def_108)))
(let ((.def_118 (and .def_109 .def_111)))
(let ((.def_119 (and .def_62 .def_118)))
(let ((.def_110 (not .def_109)))
(let ((.def_112 (and .def_110 .def_111)))
(let ((.def_103 (bvmul (_ bv100 32) x__2$main)))
(let ((.def_104 (bvslt z__6$main .def_103)))
(let ((.def_115 (and .def_104 .def_112)))
(let ((.def_116 (and .def_62 .def_115)))
(let ((.def_105 (not .def_104)))
(let ((.def_113 (and .def_105 .def_112)))
(let ((.def_101 (bvneg y__4$main)))
(let ((.def_102 (= y__4$main.next .def_101)))
(let ((.def_114 (and .def_102 .def_113)))
(let ((.def_117 (or .def_114 .def_116)))
(let ((.def_120 (or .def_117 .def_119)))
(let ((.def_121 (and .def_57 .def_120)))
(let ((.def_89 (not .def_88)))
(let ((.def_91 (and .def_89 .def_90)))
(let ((.def_46 (bvslt x__2$main (_ bv4 32))))
(let ((.def_97 (and .def_46 .def_91)))
(let ((.def_98 (and .def_57 .def_97)))
(let ((.def_99 (and .def_62 .def_98)))
(let ((.def_94 (bvadd (_ bv1 32) y__4$main)))
(let ((.def_95 (= y__4$main.next .def_94)))
(let ((.def_47 (not .def_46)))
(let ((.def_92 (and .def_47 .def_91)))
(let ((.def_80 (bvadd (_ bv1 32) x__2$main)))
(let ((.def_81 (= x__2$main.next .def_80)))
(let ((.def_93 (and .def_81 .def_92)))
(let ((.def_96 (and .def_93 .def_95)))
(let ((.def_100 (or .def_96 .def_99)))
(let ((.def_122 (or .def_100 .def_121)))
(let ((.def_84 (bvadd (_ bv100 32) y__4$main)))
(let ((.def_85 (= y__4$main.next .def_84)))
(let ((.def_74 (not .def_73)))
(let ((.def_78 (and .def_74 .def_77)))
(let ((.def_82 (and .def_78 .def_81)))
(let ((.def_86 (and .def_82 .def_85)))
(let ((.def_123 (or .def_86 .def_122)))
(let ((.def_126 (and .def_123 .def_125)))
(let ((.def_129 (and .def_126 .def_128)))
(let ((.def_130 (and .def_31 .def_129)))
(let ((.def_38 (and .def_36 .PC.0.next)))
(let ((.def_34 (not .PC.2.next)))
(let ((.def_39 (and .def_34 .def_38)))
(let ((.def_131 (and .def_39 .def_130)))
(let ((.def_68 (and .PC.0 .def_12)))
(let ((.def_69 (and .def_15 .def_68)))
(let ((.def_132 (and .def_69 .def_131)))
(let ((.def_65 (and .PC.1.next .def_64)))
(let ((.def_66 (and .def_34 .def_65)))
(let ((.def_51 (bvslt y__4$main (_ bv3 32))))
(let ((.def_43 (= |__NONDET__11$main#0| (_ bv0 32))))
(let ((.def_48 (and .def_43 .def_47)))
(let ((.def_52 (and .def_48 .def_51)))
(let ((.def_53 (and .def_31 .def_52)))
(let ((.def_56 (and .def_53 .def_55)))
(let ((.def_58 (and .def_56 .def_57)))
(let ((.def_61 (and .def_58 .def_60)))
(let ((.def_63 (and .def_61 .def_62)))
(let ((.def_67 (and .def_63 .def_66)))
(let ((.def_70 (and .def_67 .def_69)))
(let ((.def_27 (= w__8$main.next (_ bv0 32))))
(let ((.def_24 (= z__6$main.next (_ bv0 32))))
(let ((.def_21 (= y__4$main.next (_ bv0 32))))
(let ((.def_19 (= x__2$main.next (_ bv0 32))))
(let ((.def_22 (and .def_19 .def_21)))
(let ((.def_25 (and .def_22 .def_24)))
(let ((.def_28 (and .def_25 .def_27)))
(let ((.def_32 (and .def_28 .def_31)))
(let ((.def_40 (and .def_32 .def_39)))
(let ((.def_16 (and .def_13 .def_15)))
(let ((.def_41 (and .def_16 .def_40)))
(let ((.def_71 (or .def_41 .def_70)))
(let ((.def_133 (or .def_71 .def_132)))
(let ((.def_144 (or .def_133 .def_143)))
(let ((.def_147 (or .def_144 .def_146)))
.def_147)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (state |.PC.0.next| |.PC.1.next| |.PC.2.next| |__RET__$main.next| |x__2$main.next| |y__4$main.next| |z__6$main.next| |w__8$main.next|))))
(assert (forall ((|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|z__6$main| (_ BitVec 32)) (|z__6$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|x__2$main| (_ BitVec 32)) (|x__2$main.next| (_ BitVec 32)) (|w__8$main| (_ BitVec 32)) (|w__8$main.next| (_ BitVec 32)) (|y__4$main| (_ BitVec 32)) (|y__4$main.next| (_ BitVec 32)) (|__NONDET__11$main#2| (_ BitVec 32)) (|__NONDET__12$main#3| (_ BitVec 32)) (|__NONDET__13$main#4| (_ BitVec 32)) (|__NONDET__11$main#0| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool)) (=> (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |x__2$main| |y__4$main| |z__6$main| |w__8$main|) (let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_145 (and .def_13 .PC.2)))
(let ((.def_148 (not .def_145)))
.def_148))))))))
(check-sat)
