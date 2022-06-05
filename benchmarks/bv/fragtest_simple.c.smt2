;; translated from ./bv/fragtest_simple.c.vmt
;; original benchmark available at: https://es-static.fbk.eu/people/griggio/ic3ia/index.html
;; author: Alberto Griggio <griggio@fbk.eu>
(set-logic HORN)
(declare-fun state (Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|n__9$main| (_ BitVec 32)) (|n__9$main.next| (_ BitVec 32)) (|k__7$main| (_ BitVec 32)) (|k__7$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|j__11$main| (_ BitVec 32)) (|j__11$main.next| (_ BitVec 32)) (|i__1$main| (_ BitVec 32)) (|i__1$main.next| (_ BitVec 32)) (|pvlen__3$main| (_ BitVec 32)) (|pvlen__3$main.next| (_ BitVec 32)) (|i__1$main.SSA.1.ssa| (_ BitVec 32)) (|__NONDET_INLINE_INIT__4__7$main#0| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool)) (=> (let ((.def_15 (not .PC.2)))
(let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_16 (and .def_13 .def_15)))
.def_16))))) (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |k__7$main| |n__9$main| |j__11$main| |i__1$main| |pvlen__3$main|))))
(assert (forall ((|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|n__9$main| (_ BitVec 32)) (|n__9$main.next| (_ BitVec 32)) (|k__7$main| (_ BitVec 32)) (|k__7$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|j__11$main| (_ BitVec 32)) (|j__11$main.next| (_ BitVec 32)) (|i__1$main| (_ BitVec 32)) (|i__1$main.next| (_ BitVec 32)) (|pvlen__3$main| (_ BitVec 32)) (|pvlen__3$main.next| (_ BitVec 32)) (|i__1$main.SSA.1.ssa| (_ BitVec 32)) (|__NONDET_INLINE_INIT__4__7$main#0| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool)) (=> (and (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |k__7$main| |n__9$main| |j__11$main| |i__1$main| |pvlen__3$main|) (let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_107 (and .def_13 .PC.2)))
(let ((.def_67 (not .PC.0.next)))
(let ((.def_43 (not .PC.1.next)))
(let ((.def_102 (and .def_43 .def_67)))
(let ((.def_103 (and .PC.2.next .def_102)))
(let ((.def_108 (and .def_103 .def_107)))
(let ((.def_55 (= n__9$main.next n__9$main)))
(let ((.def_52 (= k__7$main.next k__7$main)))
(let ((.def_97 (and .def_52 .def_55)))
(let ((.def_38 (= __RET__$main __RET__$main.next)))
(let ((.def_98 (and .def_38 .def_97)))
(let ((.def_59 (= j__11$main.next j__11$main)))
(let ((.def_99 (and .def_59 .def_98)))
(let ((.def_62 (= i__1$main.next i__1$main)))
(let ((.def_100 (and .def_62 .def_99)))
(let ((.def_65 (= pvlen__3$main.next pvlen__3$main)))
(let ((.def_101 (and .def_65 .def_100)))
(let ((.def_104 (and .def_101 .def_103)))
(let ((.def_95 (and .def_10 .PC.1)))
(let ((.def_15 (not .PC.2)))
(let ((.def_96 (and .def_15 .def_95)))
(let ((.def_105 (and .def_96 .def_104)))
(let ((.def_85 (bvadd (_ bv1 32) j__11$main)))
(let ((.def_86 (= j__11$main.next .def_85)))
(let ((.def_81 (bvadd (_ bv4294967295 32) i__1$main)))
(let ((.def_82 (= i__1$main.next .def_81)))
(let ((.def_50 ((_ extract 31 31) k__7$main)))
(let ((.def_51 (= .def_50 (_ bv1 1))))
(let ((.def_79 (not .def_51)))
(let ((.def_77 (bvadd (_ bv4294967295 32) k__7$main)))
(let ((.def_78 (= k__7$main.next .def_77)))
(let ((.def_80 (and .def_78 .def_79)))
(let ((.def_83 (and .def_80 .def_82)))
(let ((.def_87 (and .def_83 .def_86)))
(let ((.def_75 (bvslt j__11$main.next n__9$main)))
(let ((.def_88 (and .def_75 .def_87)))
(let ((.def_89 (and .def_55 .def_88)))
(let ((.def_90 (and .def_38 .def_89)))
(let ((.def_91 (and .def_65 .def_90)))
(let ((.def_45 (and .def_43 .PC.0.next)))
(let ((.def_41 (not .PC.2.next)))
(let ((.def_46 (and .def_41 .def_45)))
(let ((.def_92 (and .def_46 .def_91)))
(let ((.def_71 (and .PC.0 .def_12)))
(let ((.def_72 (and .def_15 .def_71)))
(let ((.def_93 (and .def_72 .def_92)))
(let ((.def_68 (and .PC.1.next .def_67)))
(let ((.def_69 (and .def_41 .def_68)))
(let ((.def_53 (and .def_51 .def_52)))
(let ((.def_56 (and .def_53 .def_55)))
(let ((.def_57 (and .def_38 .def_56)))
(let ((.def_60 (and .def_57 .def_59)))
(let ((.def_63 (and .def_60 .def_62)))
(let ((.def_66 (and .def_63 .def_65)))
(let ((.def_70 (and .def_66 .def_69)))
(let ((.def_73 (and .def_70 .def_72)))
(let ((.def_33 (= j__11$main.next (_ bv0 32))))
(let ((.def_30 (= i__1$main.next (_ bv0 32))))
(let ((.def_28 (= i__1$main.SSA.1.ssa (_ bv0 32))))
(let ((.def_25 (= k__7$main.next (_ bv0 32))))
(let ((.def_22 (= pvlen__3$main.next |__NONDET_INLINE_INIT__4__7$main#0|)))
(let ((.def_26 (and .def_22 .def_25)))
(let ((.def_29 (and .def_26 .def_28)))
(let ((.def_31 (and .def_29 .def_30)))
(let ((.def_34 (and .def_31 .def_33)))
(let ((.def_19 (= n__9$main.next i__1$main.next)))
(let ((.def_35 (and .def_19 .def_34)))
(let ((.def_39 (and .def_35 .def_38)))
(let ((.def_47 (and .def_39 .def_46)))
(let ((.def_16 (and .def_13 .def_15)))
(let ((.def_48 (and .def_16 .def_47)))
(let ((.def_74 (or .def_48 .def_73)))
(let ((.def_94 (or .def_74 .def_93)))
(let ((.def_106 (or .def_94 .def_105)))
(let ((.def_109 (or .def_106 .def_108)))
.def_109))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (state |.PC.0.next| |.PC.1.next| |.PC.2.next| |__RET__$main.next| |k__7$main.next| |n__9$main.next| |j__11$main.next| |i__1$main.next| |pvlen__3$main.next|))))
(assert (forall ((|.PC.0.next| Bool) (|.PC.1.next| Bool) (|.PC.2.next| Bool) (|n__9$main| (_ BitVec 32)) (|n__9$main.next| (_ BitVec 32)) (|k__7$main| (_ BitVec 32)) (|k__7$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|j__11$main| (_ BitVec 32)) (|j__11$main.next| (_ BitVec 32)) (|i__1$main| (_ BitVec 32)) (|i__1$main.next| (_ BitVec 32)) (|pvlen__3$main| (_ BitVec 32)) (|pvlen__3$main.next| (_ BitVec 32)) (|i__1$main.SSA.1.ssa| (_ BitVec 32)) (|__NONDET_INLINE_INIT__4__7$main#0| (_ BitVec 32)) (|.PC.2| Bool) (|.PC.1| Bool) (|.PC.0| Bool)) (=> (state |.PC.0| |.PC.1| |.PC.2| |__RET__$main| |k__7$main| |n__9$main| |j__11$main| |i__1$main| |pvlen__3$main|) (let ((.def_12 (not .PC.1)))
(let ((.def_10 (not .PC.0)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_107 (and .def_13 .PC.2)))
(let ((.def_110 (not .def_107)))
.def_110))))))))
(check-sat)
