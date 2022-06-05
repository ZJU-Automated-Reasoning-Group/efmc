;; translated from ./bv/nest-if3.c.vmt
;; original benchmark available at: https://es-static.fbk.eu/people/griggio/ic3ia/index.html
;; author: Alberto Griggio <griggio@fbk.eu>
(set-logic HORN)
(declare-fun state (Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((|.PC.0| Bool) (|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|i__1$main.next| (_ BitVec 32)) (|i__1$main| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|NONDET| (_ BitVec 32)) (|NONDET.next| (_ BitVec 32)) (|k__3$main| (_ BitVec 32)) (|k__3$main.next| (_ BitVec 32)) (|l__7$main| (_ BitVec 32)) (|l__7$main.next| (_ BitVec 32)) (|n__5$main| (_ BitVec 32)) (|n__5$main.next| (_ BitVec 32)) (|__NONDET_INLINE_INIT__6__6$main#0| (_ BitVec 32)) (|__NONDET_INLINE_INIT__8__7$main#1| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool)) (=> (let ((.def_15 (not .PC.2)))
(let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_16 (and .def_13 .def_15)))
.def_16))))) (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |i__1$main| |n__5$main| |k__3$main| |l__7$main| |NONDET|))))
(assert (forall ((|.PC.0| Bool) (|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|i__1$main.next| (_ BitVec 32)) (|i__1$main| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|NONDET| (_ BitVec 32)) (|NONDET.next| (_ BitVec 32)) (|k__3$main| (_ BitVec 32)) (|k__3$main.next| (_ BitVec 32)) (|l__7$main| (_ BitVec 32)) (|l__7$main.next| (_ BitVec 32)) (|n__5$main| (_ BitVec 32)) (|n__5$main.next| (_ BitVec 32)) (|__NONDET_INLINE_INIT__6__6$main#0| (_ BitVec 32)) (|__NONDET_INLINE_INIT__8__7$main#1| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool)) (=> (and (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |i__1$main| |n__5$main| |k__3$main| |l__7$main| |NONDET|) (let ((.def_12 (not .PC.1)))
(let ((.def_51 (and .PC.0 .def_12)))
(let ((.def_134 (and .PC.2 .def_51)))
(let ((.def_45 (not .PC.1.next)))
(let ((.def_47 (and .def_45 .PC.0.next)))
(let ((.def_130 (and .PC.2.next .def_47)))
(let ((.def_135 (and .def_130 .def_134)))
(let ((.def_40 (= i__1$main i__1$main.next)))
(let ((.def_36 (= __RET__$main __RET__$main.next)))
(let ((.def_125 (and .def_36 .def_40)))
(let ((.def_61 (= NONDET.next NONDET)))
(let ((.def_126 (and .def_61 .def_125)))
(let ((.def_63 (= k__3$main.next k__3$main)))
(let ((.def_127 (and .def_63 .def_126)))
(let ((.def_65 (= l__7$main.next l__7$main)))
(let ((.def_128 (and .def_65 .def_127)))
(let ((.def_67 (= n__5$main.next n__5$main)))
(let ((.def_129 (and .def_67 .def_128)))
(let ((.def_131 (and .def_129 .def_130)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_124 (and .def_13 .PC.2)))
(let ((.def_132 (and .def_124 .def_131)))
(let ((.def_113 (bvadd (_ bv1 32) i__1$main)))
(let ((.def_114 (= i__1$main.next .def_113)))
(let ((.def_97 (bvslt i__1$main (_ bv1 32))))
(let ((.def_111 (not .def_97)))
(let ((.def_76 (bvslt i__1$main n__5$main)))
(let ((.def_112 (and .def_76 .def_111)))
(let ((.def_115 (and .def_112 .def_114)))
(let ((.def_116 (and .def_36 .def_115)))
(let ((.def_117 (and .def_61 .def_116)))
(let ((.def_118 (and .def_63 .def_117)))
(let ((.def_119 (and .def_65 .def_118)))
(let ((.def_120 (and .def_67 .def_119)))
(let ((.def_69 (and .PC.1.next .PC.0.next)))
(let ((.def_43 (not .PC.2.next)))
(let ((.def_70 (and .def_43 .def_69)))
(let ((.def_121 (and .def_70 .def_120)))
(let ((.def_93 (and .PC.0 .PC.1)))
(let ((.def_15 (not .PC.2)))
(let ((.def_94 (and .def_15 .def_93)))
(let ((.def_122 (and .def_94 .def_121)))
(let ((.def_105 (not .PC.0.next)))
(let ((.def_106 (and .def_45 .def_105)))
(let ((.def_107 (and .PC.2.next .def_106)))
(let ((.def_98 (and .def_76 .def_97)))
(let ((.def_99 (and .def_36 .def_98)))
(let ((.def_100 (and .def_40 .def_99)))
(let ((.def_101 (and .def_61 .def_100)))
(let ((.def_102 (and .def_63 .def_101)))
(let ((.def_103 (and .def_65 .def_102)))
(let ((.def_104 (and .def_67 .def_103)))
(let ((.def_108 (and .def_104 .def_107)))
(let ((.def_109 (and .def_94 .def_108)))
(let ((.def_85 (bvadd (_ bv1 32) k__3$main)))
(let ((.def_86 (= k__3$main.next .def_85)))
(let ((.def_77 (not .def_76)))
(let ((.def_74 (= NONDET (_ bv0 32))))
(let ((.def_82 (and .def_74 .def_77)))
(let ((.def_83 (and .def_65 .def_82)))
(let ((.def_79 (bvadd (_ bv1 32) l__7$main)))
(let ((.def_80 (= l__7$main.next .def_79)))
(let ((.def_75 (not .def_74)))
(let ((.def_78 (and .def_75 .def_77)))
(let ((.def_81 (and .def_78 .def_80)))
(let ((.def_84 (or .def_81 .def_83)))
(let ((.def_87 (and .def_84 .def_86)))
(let ((.def_88 (and .def_36 .def_87)))
(let ((.def_89 (and .def_40 .def_88)))
(let ((.def_90 (and .def_61 .def_89)))
(let ((.def_91 (and .def_67 .def_90)))
(let ((.def_48 (and .def_43 .def_47)))
(let ((.def_92 (and .def_48 .def_91)))
(let ((.def_95 (and .def_92 .def_94)))
(let ((.def_57 (= i__1$main.next l__7$main)))
(let ((.def_55 (bvslt k__3$main n__5$main)))
(let ((.def_58 (and .def_55 .def_57)))
(let ((.def_59 (and .def_36 .def_58)))
(let ((.def_62 (and .def_59 .def_61)))
(let ((.def_64 (and .def_62 .def_63)))
(let ((.def_66 (and .def_64 .def_65)))
(let ((.def_68 (and .def_66 .def_67)))
(let ((.def_71 (and .def_68 .def_70)))
(let ((.def_52 (and .def_15 .def_51)))
(let ((.def_72 (and .def_52 .def_71)))
(let ((.def_32 (= k__3$main.next (_ bv1 32))))
(let ((.def_28 (bvslt (_ bv0 32) l__7$main.next)))
(let ((.def_25 (= NONDET.next (_ bv0 32))))
(let ((.def_22 (= n__5$main.next |__NONDET_INLINE_INIT__6__6$main#0|)))
(let ((.def_26 (and .def_22 .def_25)))
(let ((.def_19 (= l__7$main.next |__NONDET_INLINE_INIT__8__7$main#1|)))
(let ((.def_27 (and .def_19 .def_26)))
(let ((.def_29 (and .def_27 .def_28)))
(let ((.def_33 (and .def_29 .def_32)))
(let ((.def_37 (and .def_33 .def_36)))
(let ((.def_41 (and .def_37 .def_40)))
(let ((.def_49 (and .def_41 .def_48)))
(let ((.def_16 (and .def_13 .def_15)))
(let ((.def_50 (and .def_16 .def_49)))
(let ((.def_73 (or .def_50 .def_72)))
(let ((.def_96 (or .def_73 .def_95)))
(let ((.def_110 (or .def_96 .def_109)))
(let ((.def_123 (or .def_110 .def_122)))
(let ((.def_133 (or .def_123 .def_132)))
(let ((.def_136 (or .def_133 .def_135)))
.def_136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (state |.PC.0.next| |.PC.1.next| |.PC.2.next| |__RET__$main.next| |i__1$main.next| |n__5$main.next| |k__3$main.next| |l__7$main.next| |NONDET.next|))))
(assert (forall ((|.PC.0| Bool) (|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|i__1$main.next| (_ BitVec 32)) (|i__1$main| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|NONDET| (_ BitVec 32)) (|NONDET.next| (_ BitVec 32)) (|k__3$main| (_ BitVec 32)) (|k__3$main.next| (_ BitVec 32)) (|l__7$main| (_ BitVec 32)) (|l__7$main.next| (_ BitVec 32)) (|n__5$main| (_ BitVec 32)) (|n__5$main.next| (_ BitVec 32)) (|__NONDET_INLINE_INIT__6__6$main#0| (_ BitVec 32)) (|__NONDET_INLINE_INIT__8__7$main#1| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool)) (=> (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |i__1$main| |n__5$main| |k__3$main| |l__7$main| |NONDET|) (let ((.def_12 (not .PC.1)))
(let ((.def_51 (and .PC.0 .def_12)))
(let ((.def_134 (and .PC.2 .def_51)))
(let ((.def_137 (not .def_134)))
.def_137)))))))
(check-sat)
