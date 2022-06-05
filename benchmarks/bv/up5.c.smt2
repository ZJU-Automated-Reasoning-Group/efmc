;; translated from ./bv/up5.c.vmt
;; original benchmark available at: https://es-static.fbk.eu/people/griggio/ic3ia/index.html
;; author: Alberto Griggio <griggio@fbk.eu>
(set-logic HORN)
(declare-fun state (Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((|k__5$main| (_ BitVec 32)) (|k__5$main.next| (_ BitVec 32)) (|j__7$main| (_ BitVec 32)) (|j__7$main.next| (_ BitVec 32)) (|n__1$main| (_ BitVec 32)) (|i__3$main| (_ BitVec 32)) (|i__3$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|n__1$main.next| (_ BitVec 32)) (|.PC.1.next| Bool) (|.PC.0.next| Bool) (|.PC.2.next| Bool) (|__NONDET_INLINE_INIT__2__4$main#0| (_ BitVec 32)) (|.PC.1| Bool) (|.PC.0| Bool) (|.PC.2| Bool)) (=> (let ((.def_13 (not .PC.1)))
(let ((.def_11 (not .PC.0)))
(let ((.def_14 (and .def_11 .def_13)))
(let ((.def_15 (and .PC.2 .def_14)))
.def_15)))) (state |.PC.2| |.PC.0| |.PC.1| |j__7$main| |__RET__$main| |n__1$main| |i__3$main| |k__5$main|))))
(assert (forall ((|k__5$main| (_ BitVec 32)) (|k__5$main.next| (_ BitVec 32)) (|j__7$main| (_ BitVec 32)) (|j__7$main.next| (_ BitVec 32)) (|n__1$main| (_ BitVec 32)) (|i__3$main| (_ BitVec 32)) (|i__3$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|n__1$main.next| (_ BitVec 32)) (|.PC.1.next| Bool) (|.PC.0.next| Bool) (|.PC.2.next| Bool) (|__NONDET_INLINE_INIT__2__4$main#0| (_ BitVec 32)) (|.PC.1| Bool) (|.PC.0| Bool) (|.PC.2| Bool)) (=> (and (state |.PC.2| |.PC.0| |.PC.1| |j__7$main| |__RET__$main| |n__1$main| |i__3$main| |k__5$main|) (let ((.def_86 (bvadd (_ bv4294967295 32) k__5$main)))
(let ((.def_87 (= k__5$main.next .def_86)))
(let ((.def_82 (bvadd (_ bv2 32) j__7$main)))
(let ((.def_83 (= j__7$main.next .def_82)))
(let ((.def_81 (bvslt j__7$main n__1$main)))
(let ((.def_84 (and .def_81 .def_83)))
(let ((.def_88 (and .def_84 .def_87)))
(let ((.def_50 (= i__3$main.next i__3$main)))
(let ((.def_89 (and .def_50 .def_88)))
(let ((.def_32 (= __RET__$main __RET__$main.next)))
(let ((.def_90 (and .def_32 .def_89)))
(let ((.def_56 (= n__1$main.next n__1$main)))
(let ((.def_91 (and .def_56 .def_90)))
(let ((.def_37 (not .PC.1.next)))
(let ((.def_58 (and .PC.0.next .def_37)))
(let ((.def_40 (not .PC.2.next)))
(let ((.def_59 (and .def_40 .def_58)))
(let ((.def_92 (and .def_59 .def_91)))
(let ((.def_13 (not .PC.1)))
(let ((.def_79 (and .PC.0 .def_13)))
(let ((.def_61 (not .PC.2)))
(let ((.def_80 (and .def_61 .def_79)))
(let ((.def_93 (and .def_80 .def_92)))
(let ((.def_70 (bvadd (_ bv2 32) k__5$main)))
(let ((.def_71 (= k__5$main.next .def_70)))
(let ((.def_66 (bvadd (_ bv1 32) i__3$main)))
(let ((.def_67 (= i__3$main.next .def_66)))
(let ((.def_46 (bvslt i__3$main n__1$main)))
(let ((.def_68 (and .def_46 .def_67)))
(let ((.def_72 (and .def_68 .def_71)))
(let ((.def_28 (= j__7$main j__7$main.next)))
(let ((.def_73 (and .def_28 .def_72)))
(let ((.def_74 (and .def_32 .def_73)))
(let ((.def_75 (and .def_56 .def_74)))
(let ((.def_35 (not .PC.0.next)))
(let ((.def_38 (and .def_35 .def_37)))
(let ((.def_41 (and .def_38 .def_40)))
(let ((.def_76 (and .def_41 .def_75)))
(let ((.def_11 (not .PC.0)))
(let ((.def_14 (and .def_11 .def_13)))
(let ((.def_62 (and .def_14 .def_61)))
(let ((.def_77 (and .def_62 .def_76)))
(let ((.def_54 (= k__5$main.next k__5$main)))
(let ((.def_48 (= j__7$main.next (_ bv0 32))))
(let ((.def_47 (not .def_46)))
(let ((.def_49 (and .def_47 .def_48)))
(let ((.def_51 (and .def_49 .def_50)))
(let ((.def_52 (and .def_32 .def_51)))
(let ((.def_55 (and .def_52 .def_54)))
(let ((.def_57 (and .def_55 .def_56)))
(let ((.def_60 (and .def_57 .def_59)))
(let ((.def_63 (and .def_60 .def_62)))
(let ((.def_24 (= k__5$main.next (_ bv0 32))))
(let ((.def_21 (= i__3$main.next (_ bv0 32))))
(let ((.def_18 (= n__1$main.next |__NONDET_INLINE_INIT__2__4$main#0|)))
(let ((.def_22 (and .def_18 .def_21)))
(let ((.def_25 (and .def_22 .def_24)))
(let ((.def_29 (and .def_25 .def_28)))
(let ((.def_33 (and .def_29 .def_32)))
(let ((.def_42 (and .def_33 .def_41)))
(let ((.def_15 (and .PC.2 .def_14)))
(let ((.def_43 (and .def_15 .def_42)))
(let ((.def_64 (or .def_43 .def_63)))
(let ((.def_78 (or .def_64 .def_77)))
(let ((.def_94 (or .def_78 .def_93)))
.def_94)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (state |.PC.2.next| |.PC.0.next| |.PC.1.next| |j__7$main.next| |__RET__$main.next| |n__1$main.next| |i__3$main.next| |k__5$main.next|))))
(assert (forall ((|k__5$main| (_ BitVec 32)) (|k__5$main.next| (_ BitVec 32)) (|j__7$main| (_ BitVec 32)) (|j__7$main.next| (_ BitVec 32)) (|n__1$main| (_ BitVec 32)) (|i__3$main| (_ BitVec 32)) (|i__3$main.next| (_ BitVec 32)) (|__RET__$main.next| (_ BitVec 32)) (|__RET__$main| (_ BitVec 32)) (|n__1$main.next| (_ BitVec 32)) (|.PC.1.next| Bool) (|.PC.0.next| Bool) (|.PC.2.next| Bool) (|__NONDET_INLINE_INIT__2__4$main#0| (_ BitVec 32)) (|.PC.1| Bool) (|.PC.0| Bool) (|.PC.2| Bool)) (=> (state |.PC.2| |.PC.0| |.PC.1| |j__7$main| |__RET__$main| |n__1$main| |i__3$main| |k__5$main|) (let ((.def_95 (and .PC.0 .PC.1)))
(let ((.def_61 (not .PC.2)))
(let ((.def_96 (and .def_61 .def_95)))
(let ((.def_97 (not .def_96)))
.def_97)))))))
(check-sat)
