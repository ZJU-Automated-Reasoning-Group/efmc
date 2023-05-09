(set-logic LIA)

(define-fun __node_init_Sofar_0 ((Sofar.usr.X_a_0 Bool) (Sofar.usr.Sofar_a_0 Bool) (Sofar.res.init_flag_a_0 Bool)) Bool
    (and (= Sofar.usr.Sofar_a_0 Sofar.usr.X_a_0) Sofar.res.init_flag_a_0))
(define-fun __node_trans_Sofar_0 ((Sofar.usr.X_a_1 Bool) (Sofar.usr.Sofar_a_1 Bool) (Sofar.res.init_flag_a_1 Bool) (Sofar.usr.X_a_0 Bool) (Sofar.usr.Sofar_a_0 Bool) (Sofar.res.init_flag_a_0 Bool)) Bool
    (and (= Sofar.usr.Sofar_a_1 (and Sofar.usr.X_a_1 Sofar.usr.Sofar_a_0)) (not Sofar.res.init_flag_a_1)))
(define-fun __node_init_excludes12_0 ((excludes12.usr.X1_a_0 Bool) (excludes12.usr.X2_a_0 Bool) (excludes12.usr.X3_a_0 Bool) (excludes12.usr.X4_a_0 Bool) (excludes12.usr.X5_a_0 Bool) (excludes12.usr.X6_a_0 Bool) (excludes12.usr.X7_a_0 Bool) (excludes12.usr.X8_a_0 Bool) (excludes12.usr.X9_a_0 Bool) (excludes12.usr.X10_a_0 Bool) (excludes12.usr.X11_a_0 Bool) (excludes12.usr.X12_a_0 Bool) (excludes12.usr.excludes_a_0 Bool) (excludes12.res.init_flag_a_0 Bool)) Bool
    (and (= excludes12.usr.excludes_a_0 (or (or (or (or (or (or (or (or (or (or (or (or (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0)) (and (and (and (and (and (and (and (and (and (and (and excludes12.usr.X1_a_0 (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) excludes12.usr.X2_a_0) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) excludes12.usr.X3_a_0) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) excludes12.usr.X4_a_0) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) excludes12.usr.X5_a_0) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) excludes12.usr.X6_a_0) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) excludes12.usr.X7_a_0) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) excludes12.usr.X8_a_0) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) excludes12.usr.X9_a_0) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) excludes12.usr.X10_a_0) (not excludes12.usr.X11_a_0)) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) excludes12.usr.X11_a_0) (not excludes12.usr.X12_a_0))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_0) (not excludes12.usr.X2_a_0)) (not excludes12.usr.X3_a_0)) (not excludes12.usr.X4_a_0)) (not excludes12.usr.X5_a_0)) (not excludes12.usr.X6_a_0)) (not excludes12.usr.X7_a_0)) (not excludes12.usr.X8_a_0)) (not excludes12.usr.X9_a_0)) (not excludes12.usr.X10_a_0)) (not excludes12.usr.X11_a_0)) excludes12.usr.X12_a_0))) excludes12.res.init_flag_a_0))
(define-fun __node_trans_excludes12_0 ((excludes12.usr.X1_a_1 Bool) (excludes12.usr.X2_a_1 Bool) (excludes12.usr.X3_a_1 Bool) (excludes12.usr.X4_a_1 Bool) (excludes12.usr.X5_a_1 Bool) (excludes12.usr.X6_a_1 Bool) (excludes12.usr.X7_a_1 Bool) (excludes12.usr.X8_a_1 Bool) (excludes12.usr.X9_a_1 Bool) (excludes12.usr.X10_a_1 Bool) (excludes12.usr.X11_a_1 Bool) (excludes12.usr.X12_a_1 Bool) (excludes12.usr.excludes_a_1 Bool) (excludes12.res.init_flag_a_1 Bool) (excludes12.usr.X1_a_0 Bool) (excludes12.usr.X2_a_0 Bool) (excludes12.usr.X3_a_0 Bool) (excludes12.usr.X4_a_0 Bool) (excludes12.usr.X5_a_0 Bool) (excludes12.usr.X6_a_0 Bool) (excludes12.usr.X7_a_0 Bool) (excludes12.usr.X8_a_0 Bool) (excludes12.usr.X9_a_0 Bool) (excludes12.usr.X10_a_0 Bool) (excludes12.usr.X11_a_0 Bool) (excludes12.usr.X12_a_0 Bool) (excludes12.usr.excludes_a_0 Bool) (excludes12.res.init_flag_a_0 Bool)) Bool
    (and (= excludes12.usr.excludes_a_1 (or (or (or (or (or (or (or (or (or (or (or (or (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1)) (and (and (and (and (and (and (and (and (and (and (and excludes12.usr.X1_a_1 (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) excludes12.usr.X2_a_1) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) excludes12.usr.X3_a_1) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) excludes12.usr.X4_a_1) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) excludes12.usr.X5_a_1) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) excludes12.usr.X6_a_1) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) excludes12.usr.X7_a_1) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) excludes12.usr.X8_a_1) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) excludes12.usr.X9_a_1) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) excludes12.usr.X10_a_1) (not excludes12.usr.X11_a_1)) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) excludes12.usr.X11_a_1) (not excludes12.usr.X12_a_1))) (and (and (and (and (and (and (and (and (and (and (and (not excludes12.usr.X1_a_1) (not excludes12.usr.X2_a_1)) (not excludes12.usr.X3_a_1)) (not excludes12.usr.X4_a_1)) (not excludes12.usr.X5_a_1)) (not excludes12.usr.X6_a_1)) (not excludes12.usr.X7_a_1)) (not excludes12.usr.X8_a_1)) (not excludes12.usr.X9_a_1)) (not excludes12.usr.X10_a_1)) (not excludes12.usr.X11_a_1)) excludes12.usr.X12_a_1))) (not excludes12.res.init_flag_a_1)))
(define-fun __node_init_peterson_0 ((peterson.usr.e01_a_0 Bool) (peterson.usr.e02_a_0 Bool) (peterson.usr.e03_a_0 Bool) (peterson.usr.e04_a_0 Bool) (peterson.usr.e05_a_0 Bool) (peterson.usr.e06_a_0 Bool) (peterson.usr.e07_a_0 Bool) (peterson.usr.e08_a_0 Bool) (peterson.usr.e09_a_0 Bool) (peterson.usr.e10_a_0 Bool) (peterson.usr.e11_a_0 Bool) (peterson.usr.e12_a_0 Bool) (peterson.res.nondet_23 Int) (peterson.res.nondet_22 Int) (peterson.res.nondet_21 Int) (peterson.res.nondet_20 Int) (peterson.res.nondet_19 Int) (peterson.res.nondet_18 Int) (peterson.res.nondet_17 Int) (peterson.res.nondet_16 Int) (peterson.res.nondet_15 Int) (peterson.res.nondet_14 Int) (peterson.res.nondet_13 Int) (peterson.res.nondet_12 Int) (peterson.res.nondet_11 Int) (peterson.res.nondet_10 Int) (peterson.res.nondet_9 Int) (peterson.res.nondet_8 Int) (peterson.res.nondet_7 Int) (peterson.res.nondet_6 Int) (peterson.res.nondet_5 Int) (peterson.res.nondet_4 Int) (peterson.res.nondet_3 Int) (peterson.res.nondet_2 Int) (peterson.res.nondet_1 Int) (peterson.res.nondet_0 Int) (peterson.usr.x0_a_0 Int) (peterson.usr.x1_a_0 Int) (peterson.usr.x2_a_0 Int) (peterson.usr.x3_a_0 Int) (peterson.usr.x4_a_0 Int) (peterson.usr.x5_a_0 Int) (peterson.usr.x6_a_0 Int) (peterson.usr.x7_a_0 Int) (peterson.usr.x8_a_0 Int) (peterson.usr.x9_a_0 Int) (peterson.usr.x10_a_0 Int) (peterson.usr.x11_a_0 Int) (peterson.usr.x12_a_0 Int) (peterson.usr.x13_a_0 Int) (peterson.res.init_flag_a_0 Bool)) Bool
    (and (= peterson.usr.x0_a_0 1) (let ((X1 (let ((X1 peterson.res.nondet_1) (X2 peterson.res.nondet_0)) (and (>= X2 1) (>= X1 1))))) (and (= peterson.usr.x4_a_0 1) (let ((X2 (let ((X2 peterson.res.nondet_11) (X3 peterson.res.nondet_10)) (and (>= X3 1) (>= X2 1))))) (and (= peterson.usr.x3_a_0 0) (let ((X3 (let ((X3 peterson.res.nondet_7) (X4 peterson.res.nondet_6)) (and (>= X4 1) (>= X3 1))))) (and (= peterson.usr.x2_a_0 0) (let ((X4 (let ((X4 peterson.res.nondet_3) (X5 peterson.res.nondet_2)) (and (>= X5 1) (>= X4 1))))) (and (= peterson.usr.x1_a_0 0) (let ((X5 (let ((X5 peterson.res.nondet_5) (X6 peterson.res.nondet_4)) (and (>= X6 1) (>= X5 1))))) (and (= peterson.usr.x7_a_0 1) (let ((X6 (let ((X6 peterson.res.nondet_15) (X7 peterson.res.nondet_14)) (and (>= X7 1) (>= X6 1))))) (and (= peterson.usr.x11_a_0 0) (let ((X7 (let ((X7 peterson.res.nondet_13) (X8 peterson.res.nondet_12)) (and (>= X8 1) (>= X7 1))))) (and (= peterson.usr.x9_a_0 1) (let ((X8 (let ((X8 peterson.res.nondet_23) (X9 peterson.res.nondet_22)) (and (>= X9 1) (>= X8 1))))) (and (= peterson.usr.x8_a_0 0) (= peterson.usr.x13_a_0 0) (let ((X9 (let ((X9 peterson.res.nondet_19) (X10 peterson.res.nondet_18)) (and (>= X10 1) (>= X9 1))))) (and (= peterson.usr.x12_a_0 0) (let ((X10 (let ((X10 peterson.res.nondet_17) (X11 peterson.res.nondet_16)) (and (>= X11 1) (>= X10 1))))) (and (= peterson.usr.x6_a_0 0) (let ((X11 (let ((X11 peterson.res.nondet_21) (X12 peterson.res.nondet_20)) (and (>= X12 1) (>= X11 1))))) (and (= peterson.usr.x10_a_0 1) (let ((X12 (let ((X12 peterson.res.nondet_9) (X13 peterson.res.nondet_8)) (and (>= X13 1) (>= X12 1))))) (and (= peterson.usr.x5_a_0 0) peterson.res.init_flag_a_0))))))))))))))))))))))))))
(define-fun __node_trans_peterson_0 ((peterson.usr.e01_a_1 Bool) (peterson.usr.e02_a_1 Bool) (peterson.usr.e03_a_1 Bool) (peterson.usr.e04_a_1 Bool) (peterson.usr.e05_a_1 Bool) (peterson.usr.e06_a_1 Bool) (peterson.usr.e07_a_1 Bool) (peterson.usr.e08_a_1 Bool) (peterson.usr.e09_a_1 Bool) (peterson.usr.e10_a_1 Bool) (peterson.usr.e11_a_1 Bool) (peterson.usr.e12_a_1 Bool) (peterson.res.nondet_23 Int) (peterson.res.nondet_22 Int) (peterson.res.nondet_21 Int) (peterson.res.nondet_20 Int) (peterson.res.nondet_19 Int) (peterson.res.nondet_18 Int) (peterson.res.nondet_17 Int) (peterson.res.nondet_16 Int) (peterson.res.nondet_15 Int) (peterson.res.nondet_14 Int) (peterson.res.nondet_13 Int) (peterson.res.nondet_12 Int) (peterson.res.nondet_11 Int) (peterson.res.nondet_10 Int) (peterson.res.nondet_9 Int) (peterson.res.nondet_8 Int) (peterson.res.nondet_7 Int) (peterson.res.nondet_6 Int) (peterson.res.nondet_5 Int) (peterson.res.nondet_4 Int) (peterson.res.nondet_3 Int) (peterson.res.nondet_2 Int) (peterson.res.nondet_1 Int) (peterson.res.nondet_0 Int) (peterson.usr.x0_a_1 Int) (peterson.usr.x1_a_1 Int) (peterson.usr.x2_a_1 Int) (peterson.usr.x3_a_1 Int) (peterson.usr.x4_a_1 Int) (peterson.usr.x5_a_1 Int) (peterson.usr.x6_a_1 Int) (peterson.usr.x7_a_1 Int) (peterson.usr.x8_a_1 Int) (peterson.usr.x9_a_1 Int) (peterson.usr.x10_a_1 Int) (peterson.usr.x11_a_1 Int) (peterson.usr.x12_a_1 Int) (peterson.usr.x13_a_1 Int) (peterson.res.init_flag_a_1 Bool) (peterson.usr.e01_a_0 Bool) (peterson.usr.e02_a_0 Bool) (peterson.usr.e03_a_0 Bool) (peterson.usr.e04_a_0 Bool) (peterson.usr.e05_a_0 Bool) (peterson.usr.e06_a_0 Bool) (peterson.usr.e07_a_0 Bool) (peterson.usr.e08_a_0 Bool) (peterson.usr.e09_a_0 Bool) (peterson.usr.e10_a_0 Bool) (peterson.usr.e11_a_0 Bool) (peterson.usr.e12_a_0 Bool) (peterson.usr.x0_a_0 Int) (peterson.usr.x1_a_0 Int) (peterson.usr.x2_a_0 Int) (peterson.usr.x3_a_0 Int) (peterson.usr.x4_a_0 Int) (peterson.usr.x5_a_0 Int) (peterson.usr.x6_a_0 Int) (peterson.usr.x7_a_0 Int) (peterson.usr.x8_a_0 Int) (peterson.usr.x9_a_0 Int) (peterson.usr.x10_a_0 Int) (peterson.usr.x11_a_0 Int) (peterson.usr.x12_a_0 Int) (peterson.usr.x13_a_0 Int) (peterson.res.init_flag_a_0 Bool)) Bool
    (let ((X1 (and (>= peterson.usr.x3_a_0 1) (>= peterson.usr.x5_a_0 1)))) (let ((X2 (and (>= peterson.usr.x0_a_0 1) (>= peterson.usr.x4_a_0 1)))) (and (= peterson.usr.x0_a_1 (ite peterson.usr.e01_a_1 (ite X2 (- peterson.usr.x0_a_0 1) peterson.usr.x0_a_0) (ite peterson.usr.e06_a_1 (ite X1 (+ peterson.usr.x0_a_0 1) peterson.usr.x0_a_0) peterson.usr.x0_a_0))) (= peterson.usr.x4_a_1 (ite peterson.usr.e01_a_1 (ite X2 (- peterson.usr.x4_a_0 1) peterson.usr.x4_a_0) (ite peterson.usr.e06_a_1 (ite X1 (+ peterson.usr.x4_a_0 1) peterson.usr.x4_a_0) peterson.usr.x4_a_0))) (let ((X3 (and (>= peterson.usr.x2_a_0 1) (>= peterson.usr.x6_a_0 1)))) (let ((X4 (and (>= peterson.usr.x2_a_0 1) (>= peterson.usr.x9_a_0 1)))) (and (= peterson.usr.x3_a_1 (ite peterson.usr.e04_a_1 (ite X4 (+ peterson.usr.x3_a_0 1) peterson.usr.x3_a_0) (ite peterson.usr.e05_a_1 (ite X3 (+ peterson.usr.x3_a_0 1) peterson.usr.x3_a_0) (ite peterson.usr.e06_a_1 (ite X1 (- peterson.usr.x3_a_0 1) peterson.usr.x3_a_0) peterson.usr.x3_a_0)))) (let ((X5 (and (>= peterson.usr.x1_a_0 1) (>= peterson.usr.x7_a_0 1)))) (let ((X6 (and (>= peterson.usr.x1_a_0 1) (>= peterson.usr.x6_a_0 1)))) (and (= peterson.usr.x2_a_1 (ite peterson.usr.e02_a_1 (ite X6 (+ peterson.usr.x2_a_0 1) peterson.usr.x2_a_0) (ite peterson.usr.e03_a_1 (ite X5 (+ peterson.usr.x2_a_0 1) peterson.usr.x2_a_0) (ite peterson.usr.e04_a_1 (ite X4 (- peterson.usr.x2_a_0 1) peterson.usr.x2_a_0) (ite peterson.usr.e05_a_1 (ite X3 (- peterson.usr.x2_a_0 1) peterson.usr.x2_a_0) peterson.usr.x2_a_0))))) (= peterson.usr.x1_a_1 (ite peterson.usr.e01_a_1 (ite X2 (+ peterson.usr.x1_a_0 1) peterson.usr.x1_a_0) (ite peterson.usr.e02_a_1 (ite X6 (- peterson.usr.x1_a_0 1) peterson.usr.x1_a_0) (ite peterson.usr.e03_a_1 (ite X5 (- peterson.usr.x1_a_0 1) peterson.usr.x1_a_0) peterson.usr.x1_a_0)))) (let ((X7 (and (>= peterson.usr.x7_a_0 1) (>= peterson.usr.x11_a_0 1)))) (and (= peterson.usr.x7_a_1 (ite peterson.usr.e02_a_1 (ite X6 (+ peterson.usr.x7_a_0 1) peterson.usr.x7_a_0) (ite peterson.usr.e08_a_1 (ite X7 (- peterson.usr.x7_a_0 1) peterson.usr.x7_a_0) peterson.usr.x7_a_0))) (let ((X8 (and (>= peterson.usr.x6_a_0 1) (>= peterson.usr.x11_a_0 1)))) (let ((X9 (and (>= peterson.usr.x9_a_0 1) (>= peterson.usr.x10_a_0 1)))) (and (= peterson.usr.x11_a_1 (ite peterson.usr.e07_a_1 (ite X9 (+ peterson.usr.x11_a_0 1) peterson.usr.x11_a_0) (ite peterson.usr.e08_a_1 (ite X7 (- peterson.usr.x11_a_0 1) peterson.usr.x11_a_0) (ite peterson.usr.e09_a_1 (ite X8 (- peterson.usr.x11_a_0 1) peterson.usr.x11_a_0) peterson.usr.x11_a_0)))) (let ((X10 (and (>= peterson.usr.x8_a_0 1) (>= peterson.usr.x13_a_0 1)))) (and (= peterson.usr.x9_a_1 (ite peterson.usr.e07_a_1 (ite X9 (- peterson.usr.x9_a_0 1) peterson.usr.x9_a_0) (ite peterson.usr.e12_a_1 (ite X10 (+ peterson.usr.x9_a_0 1) peterson.usr.x9_a_0) peterson.usr.x9_a_0))) (= peterson.usr.x8_a_1 (ite peterson.usr.e07_a_1 (ite X9 (+ peterson.usr.x8_a_0 1) peterson.usr.x8_a_0) (ite peterson.usr.e12_a_1 (ite X10 (- peterson.usr.x8_a_0 1) peterson.usr.x8_a_0) peterson.usr.x8_a_0))) (let ((X11 (and (>= peterson.usr.x7_a_0 1) (>= peterson.usr.x12_a_0 1)))) (let ((X12 (and (>= peterson.usr.x4_a_0 1) (>= peterson.usr.x12_a_0 1)))) (and (= peterson.usr.x13_a_1 (ite peterson.usr.e10_a_1 (ite X12 (+ peterson.usr.x13_a_0 1) peterson.usr.x13_a_0) (ite peterson.usr.e11_a_1 (ite X11 (+ peterson.usr.x13_a_0 1) peterson.usr.x13_a_0) (ite peterson.usr.e12_a_1 (ite X10 (- peterson.usr.x13_a_0 1) peterson.usr.x13_a_0) peterson.usr.x13_a_0)))) (= peterson.usr.x12_a_1 (ite peterson.usr.e08_a_1 (ite X7 (+ peterson.usr.x12_a_0 1) peterson.usr.x12_a_0) (ite peterson.usr.e09_a_1 (ite X8 (+ peterson.usr.x12_a_0 1) peterson.usr.x12_a_0) (ite peterson.usr.e10_a_1 (ite X12 (- peterson.usr.x12_a_0 1) peterson.usr.x12_a_0) (ite peterson.usr.e11_a_1 (ite X11 (- peterson.usr.x12_a_0 1) peterson.usr.x12_a_0) peterson.usr.x12_a_0))))) (= peterson.usr.x6_a_1 (ite peterson.usr.e02_a_1 (ite X6 (- peterson.usr.x6_a_0 1) peterson.usr.x6_a_0) (ite peterson.usr.e08_a_1 (ite X7 (+ peterson.usr.x6_a_0 1) peterson.usr.x6_a_0) peterson.usr.x6_a_0))) (= peterson.usr.x10_a_1 (ite peterson.usr.e07_a_1 (ite X9 (- peterson.usr.x10_a_0 1) peterson.usr.x10_a_0) (ite peterson.usr.e12_a_1 (ite X10 (+ peterson.usr.x10_a_0 1) peterson.usr.x10_a_0) peterson.usr.x10_a_0))) (= peterson.usr.x5_a_1 (ite peterson.usr.e01_a_1 (ite X2 (+ peterson.usr.x5_a_0 1) peterson.usr.x5_a_0) (ite peterson.usr.e06_a_1 (ite X1 (- peterson.usr.x5_a_0 1) peterson.usr.x5_a_0) peterson.usr.x5_a_0))) (not peterson.res.init_flag_a_1)))))))))))))))))))))
(define-fun __node_init_top_0 ((top.usr.e01_a_0 Bool) (top.usr.e02_a_0 Bool) (top.usr.e03_a_0 Bool) (top.usr.e04_a_0 Bool) (top.usr.e05_a_0 Bool) (top.usr.e06_a_0 Bool) (top.usr.e07_a_0 Bool) (top.usr.e08_a_0 Bool) (top.usr.e09_a_0 Bool) (top.usr.e10_a_0 Bool) (top.usr.e11_a_0 Bool) (top.usr.e12_a_0 Bool) (top.res.nondet_23 Int) (top.res.nondet_22 Int) (top.res.nondet_21 Int) (top.res.nondet_20 Int) (top.res.nondet_19 Int) (top.res.nondet_18 Int) (top.res.nondet_17 Int) (top.res.nondet_16 Int) (top.res.nondet_15 Int) (top.res.nondet_14 Int) (top.res.nondet_13 Int) (top.res.nondet_12 Int) (top.res.nondet_11 Int) (top.res.nondet_10 Int) (top.res.nondet_9 Int) (top.res.nondet_8 Int) (top.res.nondet_7 Int) (top.res.nondet_6 Int) (top.res.nondet_5 Int) (top.res.nondet_4 Int) (top.res.nondet_3 Int) (top.res.nondet_2 Int) (top.res.nondet_1 Int) (top.res.nondet_0 Int) (top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.res.abs_0_a_0 Int) (top.res.abs_1_a_0 Int) (top.res.abs_2_a_0 Int) (top.res.abs_3_a_0 Int) (top.res.abs_4_a_0 Int) (top.res.abs_5_a_0 Int) (top.res.abs_6_a_0 Int) (top.res.abs_7_a_0 Int) (top.res.abs_8_a_0 Int) (top.res.abs_9_a_0 Int) (top.res.abs_10_a_0 Int) (top.res.abs_11_a_0 Int) (top.res.abs_12_a_0 Int) (top.res.abs_13_a_0 Int) (top.res.abs_14_a_0 Bool) (top.res.abs_15_a_0 Bool) (top.res.abs_16_a_0 Bool) (top.res.inst_2_a_0 Bool) (top.res.inst_1_a_0 Bool) (top.res.inst_0_a_0 Bool)) Bool
    (let ((X1 top.res.abs_2_a_0)) (and (= top.res.abs_15_a_0 (and top.res.abs_14_a_0 (< X1 32767))) (let ((X2 top.res.abs_16_a_0)) (and (= top.usr.OK_a_0 (=> X2 (>= X1 0))) (__node_init_peterson_0 top.usr.e01_a_0 top.usr.e02_a_0 top.usr.e03_a_0 top.usr.e04_a_0 top.usr.e05_a_0 top.usr.e06_a_0 top.usr.e07_a_0 top.usr.e08_a_0 top.usr.e09_a_0 top.usr.e10_a_0 top.usr.e11_a_0 top.usr.e12_a_0 top.res.nondet_23 top.res.nondet_22 top.res.nondet_21 top.res.nondet_20 top.res.nondet_19 top.res.nondet_18 top.res.nondet_17 top.res.nondet_16 top.res.nondet_15 top.res.nondet_14 top.res.nondet_13 top.res.nondet_12 top.res.nondet_11 top.res.nondet_10 top.res.nondet_9 top.res.nondet_8 top.res.nondet_7 top.res.nondet_6 top.res.nondet_5 top.res.nondet_4 top.res.nondet_3 top.res.nondet_2 top.res.nondet_1 top.res.nondet_0 top.res.abs_0_a_0 top.res.abs_1_a_0 top.res.abs_2_a_0 top.res.abs_3_a_0 top.res.abs_4_a_0 top.res.abs_5_a_0 top.res.abs_6_a_0 top.res.abs_7_a_0 top.res.abs_8_a_0 top.res.abs_9_a_0 top.res.abs_10_a_0 top.res.abs_11_a_0 top.res.abs_12_a_0 top.res.abs_13_a_0 top.res.inst_2_a_0) (__node_init_Sofar_0 top.res.abs_15_a_0 top.res.abs_16_a_0 top.res.inst_1_a_0) (__node_init_excludes12_0 top.usr.e01_a_0 top.usr.e02_a_0 top.usr.e03_a_0 top.usr.e04_a_0 top.usr.e05_a_0 top.usr.e06_a_0 top.usr.e07_a_0 top.usr.e08_a_0 top.usr.e09_a_0 top.usr.e10_a_0 top.usr.e11_a_0 top.usr.e12_a_0 top.res.abs_14_a_0 top.res.inst_0_a_0) top.res.init_flag_a_0)))))
(define-fun __node_trans_top_0 ((top.usr.e01_a_1 Bool) (top.usr.e02_a_1 Bool) (top.usr.e03_a_1 Bool) (top.usr.e04_a_1 Bool) (top.usr.e05_a_1 Bool) (top.usr.e06_a_1 Bool) (top.usr.e07_a_1 Bool) (top.usr.e08_a_1 Bool) (top.usr.e09_a_1 Bool) (top.usr.e10_a_1 Bool) (top.usr.e11_a_1 Bool) (top.usr.e12_a_1 Bool) (top.res.nondet_23 Int) (top.res.nondet_22 Int) (top.res.nondet_21 Int) (top.res.nondet_20 Int) (top.res.nondet_19 Int) (top.res.nondet_18 Int) (top.res.nondet_17 Int) (top.res.nondet_16 Int) (top.res.nondet_15 Int) (top.res.nondet_14 Int) (top.res.nondet_13 Int) (top.res.nondet_12 Int) (top.res.nondet_11 Int) (top.res.nondet_10 Int) (top.res.nondet_9 Int) (top.res.nondet_8 Int) (top.res.nondet_7 Int) (top.res.nondet_6 Int) (top.res.nondet_5 Int) (top.res.nondet_4 Int) (top.res.nondet_3 Int) (top.res.nondet_2 Int) (top.res.nondet_1 Int) (top.res.nondet_0 Int) (top.usr.OK_a_1 Bool) (top.res.init_flag_a_1 Bool) (top.res.abs_0_a_1 Int) (top.res.abs_1_a_1 Int) (top.res.abs_2_a_1 Int) (top.res.abs_3_a_1 Int) (top.res.abs_4_a_1 Int) (top.res.abs_5_a_1 Int) (top.res.abs_6_a_1 Int) (top.res.abs_7_a_1 Int) (top.res.abs_8_a_1 Int) (top.res.abs_9_a_1 Int) (top.res.abs_10_a_1 Int) (top.res.abs_11_a_1 Int) (top.res.abs_12_a_1 Int) (top.res.abs_13_a_1 Int) (top.res.abs_14_a_1 Bool) (top.res.abs_15_a_1 Bool) (top.res.abs_16_a_1 Bool) (top.res.inst_2_a_1 Bool) (top.res.inst_1_a_1 Bool) (top.res.inst_0_a_1 Bool) (top.usr.e01_a_0 Bool) (top.usr.e02_a_0 Bool) (top.usr.e03_a_0 Bool) (top.usr.e04_a_0 Bool) (top.usr.e05_a_0 Bool) (top.usr.e06_a_0 Bool) (top.usr.e07_a_0 Bool) (top.usr.e08_a_0 Bool) (top.usr.e09_a_0 Bool) (top.usr.e10_a_0 Bool) (top.usr.e11_a_0 Bool) (top.usr.e12_a_0 Bool) (top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.res.abs_0_a_0 Int) (top.res.abs_1_a_0 Int) (top.res.abs_2_a_0 Int) (top.res.abs_3_a_0 Int) (top.res.abs_4_a_0 Int) (top.res.abs_5_a_0 Int) (top.res.abs_6_a_0 Int) (top.res.abs_7_a_0 Int) (top.res.abs_8_a_0 Int) (top.res.abs_9_a_0 Int) (top.res.abs_10_a_0 Int) (top.res.abs_11_a_0 Int) (top.res.abs_12_a_0 Int) (top.res.abs_13_a_0 Int) (top.res.abs_14_a_0 Bool) (top.res.abs_15_a_0 Bool) (top.res.abs_16_a_0 Bool) (top.res.inst_2_a_0 Bool) (top.res.inst_1_a_0 Bool) (top.res.inst_0_a_0 Bool)) Bool
    (let ((X1 top.res.abs_2_a_1)) (and (= top.res.abs_15_a_1 (and top.res.abs_14_a_1 (< X1 32767))) (let ((X2 top.res.abs_16_a_1)) (and (= top.usr.OK_a_1 (=> X2 (>= X1 0))) (__node_trans_peterson_0 top.usr.e01_a_1 top.usr.e02_a_1 top.usr.e03_a_1 top.usr.e04_a_1 top.usr.e05_a_1 top.usr.e06_a_1 top.usr.e07_a_1 top.usr.e08_a_1 top.usr.e09_a_1 top.usr.e10_a_1 top.usr.e11_a_1 top.usr.e12_a_1 top.res.nondet_23 top.res.nondet_22 top.res.nondet_21 top.res.nondet_20 top.res.nondet_19 top.res.nondet_18 top.res.nondet_17 top.res.nondet_16 top.res.nondet_15 top.res.nondet_14 top.res.nondet_13 top.res.nondet_12 top.res.nondet_11 top.res.nondet_10 top.res.nondet_9 top.res.nondet_8 top.res.nondet_7 top.res.nondet_6 top.res.nondet_5 top.res.nondet_4 top.res.nondet_3 top.res.nondet_2 top.res.nondet_1 top.res.nondet_0 top.res.abs_0_a_1 top.res.abs_1_a_1 top.res.abs_2_a_1 top.res.abs_3_a_1 top.res.abs_4_a_1 top.res.abs_5_a_1 top.res.abs_6_a_1 top.res.abs_7_a_1 top.res.abs_8_a_1 top.res.abs_9_a_1 top.res.abs_10_a_1 top.res.abs_11_a_1 top.res.abs_12_a_1 top.res.abs_13_a_1 top.res.inst_2_a_1 top.usr.e01_a_0 top.usr.e02_a_0 top.usr.e03_a_0 top.usr.e04_a_0 top.usr.e05_a_0 top.usr.e06_a_0 top.usr.e07_a_0 top.usr.e08_a_0 top.usr.e09_a_0 top.usr.e10_a_0 top.usr.e11_a_0 top.usr.e12_a_0 top.res.abs_0_a_0 top.res.abs_1_a_0 top.res.abs_2_a_0 top.res.abs_3_a_0 top.res.abs_4_a_0 top.res.abs_5_a_0 top.res.abs_6_a_0 top.res.abs_7_a_0 top.res.abs_8_a_0 top.res.abs_9_a_0 top.res.abs_10_a_0 top.res.abs_11_a_0 top.res.abs_12_a_0 top.res.abs_13_a_0 top.res.inst_2_a_0) (__node_trans_Sofar_0 top.res.abs_15_a_1 top.res.abs_16_a_1 top.res.inst_1_a_1 top.res.abs_15_a_0 top.res.abs_16_a_0 top.res.inst_1_a_0) (__node_trans_excludes12_0 top.usr.e01_a_1 top.usr.e02_a_1 top.usr.e03_a_1 top.usr.e04_a_1 top.usr.e05_a_1 top.usr.e06_a_1 top.usr.e07_a_1 top.usr.e08_a_1 top.usr.e09_a_1 top.usr.e10_a_1 top.usr.e11_a_1 top.usr.e12_a_1 top.res.abs_14_a_1 top.res.inst_0_a_1 top.usr.e01_a_0 top.usr.e02_a_0 top.usr.e03_a_0 top.usr.e04_a_0 top.usr.e05_a_0 top.usr.e06_a_0 top.usr.e07_a_0 top.usr.e08_a_0 top.usr.e09_a_0 top.usr.e10_a_0 top.usr.e11_a_0 top.usr.e12_a_0 top.res.abs_14_a_0 top.res.inst_0_a_0) (not top.res.init_flag_a_1))))))
(synth-inv str_invariant ((top.usr.e01 Bool) (top.usr.e02 Bool) (top.usr.e03 Bool) (top.usr.e04 Bool) (top.usr.e05 Bool) (top.usr.e06 Bool) (top.usr.e07 Bool) (top.usr.e08 Bool) (top.usr.e09 Bool) (top.usr.e10 Bool) (top.usr.e11 Bool) (top.usr.e12 Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.res.abs_0 Int) (top.res.abs_1 Int) (top.res.abs_2 Int) (top.res.abs_3 Int) (top.res.abs_4 Int) (top.res.abs_5 Int) (top.res.abs_6 Int) (top.res.abs_7 Int) (top.res.abs_8 Int) (top.res.abs_9 Int) (top.res.abs_10 Int) (top.res.abs_11 Int) (top.res.abs_12 Int) (top.res.abs_13 Int) (top.res.abs_14 Bool) (top.res.abs_15 Bool) (top.res.abs_16 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool)))

(declare-var top.res.nondet_23 Int)
(declare-var top.res.nondet_22 Int)
(declare-var top.res.nondet_21 Int)
(declare-var top.res.nondet_20 Int)
(declare-var top.res.nondet_19 Int)
(declare-var top.res.nondet_18 Int)
(declare-var top.res.nondet_17 Int)
(declare-var top.res.nondet_16 Int)
(declare-var top.res.nondet_15 Int)
(declare-var top.res.nondet_14 Int)
(declare-var top.res.nondet_13 Int)
(declare-var top.res.nondet_12 Int)
(declare-var top.res.nondet_11 Int)
(declare-var top.res.nondet_10 Int)
(declare-var top.res.nondet_9 Int)
(declare-var top.res.nondet_8 Int)
(declare-var top.res.nondet_7 Int)
(declare-var top.res.nondet_6 Int)
(declare-var top.res.nondet_5 Int)
(declare-var top.res.nondet_4 Int)
(declare-var top.res.nondet_3 Int)
(declare-var top.res.nondet_2 Int)
(declare-var top.res.nondet_1 Int)
(declare-var top.res.nondet_0 Int)
(define-fun init ((top.usr.e01 Bool) (top.usr.e02 Bool) (top.usr.e03 Bool) (top.usr.e04 Bool) (top.usr.e05 Bool) (top.usr.e06 Bool) (top.usr.e07 Bool) (top.usr.e08 Bool) (top.usr.e09 Bool) (top.usr.e10 Bool) (top.usr.e11 Bool) (top.usr.e12 Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.res.abs_0 Int) (top.res.abs_1 Int) (top.res.abs_2 Int) (top.res.abs_3 Int) (top.res.abs_4 Int) (top.res.abs_5 Int) (top.res.abs_6 Int) (top.res.abs_7 Int) (top.res.abs_8 Int) (top.res.abs_9 Int) (top.res.abs_10 Int) (top.res.abs_11 Int) (top.res.abs_12 Int) (top.res.abs_13 Int) (top.res.abs_14 Bool) (top.res.abs_15 Bool) (top.res.abs_16 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool)) Bool
    (let ((X1 top.res.abs_2)) (and (= top.res.abs_15 (and top.res.abs_14 (< X1 32767))) (let ((X2 top.res.abs_16)) (and (= top.usr.OK (=> X2 (>= X1 0))) (__node_init_peterson_0 top.usr.e01 top.usr.e02 top.usr.e03 top.usr.e04 top.usr.e05 top.usr.e06 top.usr.e07 top.usr.e08 top.usr.e09 top.usr.e10 top.usr.e11 top.usr.e12 top.res.nondet_23 top.res.nondet_22 top.res.nondet_21 top.res.nondet_20 top.res.nondet_19 top.res.nondet_18 top.res.nondet_17 top.res.nondet_16 top.res.nondet_15 top.res.nondet_14 top.res.nondet_13 top.res.nondet_12 top.res.nondet_11 top.res.nondet_10 top.res.nondet_9 top.res.nondet_8 top.res.nondet_7 top.res.nondet_6 top.res.nondet_5 top.res.nondet_4 top.res.nondet_3 top.res.nondet_2 top.res.nondet_1 top.res.nondet_0 top.res.abs_0 top.res.abs_1 top.res.abs_2 top.res.abs_3 top.res.abs_4 top.res.abs_5 top.res.abs_6 top.res.abs_7 top.res.abs_8 top.res.abs_9 top.res.abs_10 top.res.abs_11 top.res.abs_12 top.res.abs_13 top.res.inst_2) (__node_init_Sofar_0 top.res.abs_15 top.res.abs_16 top.res.inst_1) (__node_init_excludes12_0 top.usr.e01 top.usr.e02 top.usr.e03 top.usr.e04 top.usr.e05 top.usr.e06 top.usr.e07 top.usr.e08 top.usr.e09 top.usr.e10 top.usr.e11 top.usr.e12 top.res.abs_14 top.res.inst_0) top.res.init_flag)))))
(define-fun trans ((top.usr.e01 Bool) (top.usr.e02 Bool) (top.usr.e03 Bool) (top.usr.e04 Bool) (top.usr.e05 Bool) (top.usr.e06 Bool) (top.usr.e07 Bool) (top.usr.e08 Bool) (top.usr.e09 Bool) (top.usr.e10 Bool) (top.usr.e11 Bool) (top.usr.e12 Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.res.abs_0 Int) (top.res.abs_1 Int) (top.res.abs_2 Int) (top.res.abs_3 Int) (top.res.abs_4 Int) (top.res.abs_5 Int) (top.res.abs_6 Int) (top.res.abs_7 Int) (top.res.abs_8 Int) (top.res.abs_9 Int) (top.res.abs_10 Int) (top.res.abs_11 Int) (top.res.abs_12 Int) (top.res.abs_13 Int) (top.res.abs_14 Bool) (top.res.abs_15 Bool) (top.res.abs_16 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool) (top.usr.e01! Bool) (top.usr.e02! Bool) (top.usr.e03! Bool) (top.usr.e04! Bool) (top.usr.e05! Bool) (top.usr.e06! Bool) (top.usr.e07! Bool) (top.usr.e08! Bool) (top.usr.e09! Bool) (top.usr.e10! Bool) (top.usr.e11! Bool) (top.usr.e12! Bool) (top.usr.OK! Bool) (top.res.init_flag! Bool) (top.res.abs_0! Int) (top.res.abs_1! Int) (top.res.abs_2! Int) (top.res.abs_3! Int) (top.res.abs_4! Int) (top.res.abs_5! Int) (top.res.abs_6! Int) (top.res.abs_7! Int) (top.res.abs_8! Int) (top.res.abs_9! Int) (top.res.abs_10! Int) (top.res.abs_11! Int) (top.res.abs_12! Int) (top.res.abs_13! Int) (top.res.abs_14! Bool) (top.res.abs_15! Bool) (top.res.abs_16! Bool) (top.res.inst_2! Bool) (top.res.inst_1! Bool) (top.res.inst_0! Bool)) Bool
    (and (let ((X1 top.res.abs_2!)) (and (= top.res.abs_15! (and top.res.abs_14! (< X1 32767))) (let ((X2 top.res.abs_16!)) (and (= top.usr.OK! (=> X2 (>= X1 0))) (__node_trans_peterson_0 top.usr.e01! top.usr.e02! top.usr.e03! top.usr.e04! top.usr.e05! top.usr.e06! top.usr.e07! top.usr.e08! top.usr.e09! top.usr.e10! top.usr.e11! top.usr.e12! top.res.nondet_23 top.res.nondet_22 top.res.nondet_21 top.res.nondet_20 top.res.nondet_19 top.res.nondet_18 top.res.nondet_17 top.res.nondet_16 top.res.nondet_15 top.res.nondet_14 top.res.nondet_13 top.res.nondet_12 top.res.nondet_11 top.res.nondet_10 top.res.nondet_9 top.res.nondet_8 top.res.nondet_7 top.res.nondet_6 top.res.nondet_5 top.res.nondet_4 top.res.nondet_3 top.res.nondet_2 top.res.nondet_1 top.res.nondet_0 top.res.abs_0! top.res.abs_1! top.res.abs_2! top.res.abs_3! top.res.abs_4! top.res.abs_5! top.res.abs_6! top.res.abs_7! top.res.abs_8! top.res.abs_9! top.res.abs_10! top.res.abs_11! top.res.abs_12! top.res.abs_13! top.res.inst_2! top.usr.e01 top.usr.e02 top.usr.e03 top.usr.e04 top.usr.e05 top.usr.e06 top.usr.e07 top.usr.e08 top.usr.e09 top.usr.e10 top.usr.e11 top.usr.e12 top.res.abs_0 top.res.abs_1 top.res.abs_2 top.res.abs_3 top.res.abs_4 top.res.abs_5 top.res.abs_6 top.res.abs_7 top.res.abs_8 top.res.abs_9 top.res.abs_10 top.res.abs_11 top.res.abs_12 top.res.abs_13 top.res.inst_2) (__node_trans_Sofar_0 top.res.abs_15! top.res.abs_16! top.res.inst_1! top.res.abs_15 top.res.abs_16 top.res.inst_1) (__node_trans_excludes12_0 top.usr.e01! top.usr.e02! top.usr.e03! top.usr.e04! top.usr.e05! top.usr.e06! top.usr.e07! top.usr.e08! top.usr.e09! top.usr.e10! top.usr.e11! top.usr.e12! top.res.abs_14! top.res.inst_0! top.usr.e01 top.usr.e02 top.usr.e03 top.usr.e04 top.usr.e05 top.usr.e06 top.usr.e07 top.usr.e08 top.usr.e09 top.usr.e10 top.usr.e11 top.usr.e12 top.res.abs_14 top.res.inst_0) (not top.res.init_flag!))))) (= top.res.nondet_23 top.res.nondet_23) (= top.res.nondet_22 top.res.nondet_22) (= top.res.nondet_21 top.res.nondet_21) (= top.res.nondet_20 top.res.nondet_20) (= top.res.nondet_19 top.res.nondet_19) (= top.res.nondet_18 top.res.nondet_18) (= top.res.nondet_17 top.res.nondet_17) (= top.res.nondet_16 top.res.nondet_16) (= top.res.nondet_15 top.res.nondet_15) (= top.res.nondet_14 top.res.nondet_14) (= top.res.nondet_13 top.res.nondet_13) (= top.res.nondet_12 top.res.nondet_12) (= top.res.nondet_11 top.res.nondet_11) (= top.res.nondet_10 top.res.nondet_10) (= top.res.nondet_9 top.res.nondet_9) (= top.res.nondet_8 top.res.nondet_8) (= top.res.nondet_7 top.res.nondet_7) (= top.res.nondet_6 top.res.nondet_6) (= top.res.nondet_5 top.res.nondet_5) (= top.res.nondet_4 top.res.nondet_4) (= top.res.nondet_3 top.res.nondet_3) (= top.res.nondet_2 top.res.nondet_2) (= top.res.nondet_1 top.res.nondet_1) (= top.res.nondet_0 top.res.nondet_0)))
(define-fun prop ((top.usr.e01 Bool) (top.usr.e02 Bool) (top.usr.e03 Bool) (top.usr.e04 Bool) (top.usr.e05 Bool) (top.usr.e06 Bool) (top.usr.e07 Bool) (top.usr.e08 Bool) (top.usr.e09 Bool) (top.usr.e10 Bool) (top.usr.e11 Bool) (top.usr.e12 Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.res.abs_0 Int) (top.res.abs_1 Int) (top.res.abs_2 Int) (top.res.abs_3 Int) (top.res.abs_4 Int) (top.res.abs_5 Int) (top.res.abs_6 Int) (top.res.abs_7 Int) (top.res.abs_8 Int) (top.res.abs_9 Int) (top.res.abs_10 Int) (top.res.abs_11 Int) (top.res.abs_12 Int) (top.res.abs_13 Int) (top.res.abs_14 Bool) (top.res.abs_15 Bool) (top.res.abs_16 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool)) Bool
    top.usr.OK)

(inv-constraint str_invariant init trans prop)

(check-synth)

