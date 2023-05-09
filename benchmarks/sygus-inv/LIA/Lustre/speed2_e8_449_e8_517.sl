(set-logic LIA)

(define-fun __node_init_COUNTER_0 ((COUNTER.usr.init_a_0 Int) (COUNTER.usr.incr_a_0 Int) (COUNTER.usr.X_a_0 Bool) (COUNTER.usr.reset_a_0 Bool) (COUNTER.usr.C_a_0 Int) (COUNTER.res.init_flag_a_0 Bool)) Bool
    (let ((X1 COUNTER.usr.init_a_0)) (and (= COUNTER.usr.C_a_0 (ite COUNTER.usr.reset_a_0 COUNTER.usr.init_a_0 (ite COUNTER.usr.X_a_0 (+ X1 COUNTER.usr.incr_a_0) X1))) COUNTER.res.init_flag_a_0)))
(define-fun __node_trans_COUNTER_0 ((COUNTER.usr.init_a_1 Int) (COUNTER.usr.incr_a_1 Int) (COUNTER.usr.X_a_1 Bool) (COUNTER.usr.reset_a_1 Bool) (COUNTER.usr.C_a_1 Int) (COUNTER.res.init_flag_a_1 Bool) (COUNTER.usr.init_a_0 Int) (COUNTER.usr.incr_a_0 Int) (COUNTER.usr.X_a_0 Bool) (COUNTER.usr.reset_a_0 Bool) (COUNTER.usr.C_a_0 Int) (COUNTER.res.init_flag_a_0 Bool)) Bool
    (let ((X1 COUNTER.usr.C_a_0)) (and (= COUNTER.usr.C_a_1 (ite COUNTER.usr.reset_a_1 COUNTER.usr.init_a_1 (ite COUNTER.usr.X_a_1 (+ X1 COUNTER.usr.incr_a_1) X1))) (not COUNTER.res.init_flag_a_1))))
(define-fun __node_init_speed_0 ((speed.usr.beacon_a_0 Bool) (speed.usr.second_a_0 Bool) (speed.usr.late_a_0 Bool) (speed.usr.early_a_0 Bool) (speed.res.init_flag_a_0 Bool) (speed.impl.usr.incr_a_0 Int) (speed.res.abs_0_a_0 Int) (speed.res.abs_1_a_0 Bool) (speed.res.abs_2_a_0 Bool) (speed.res.abs_3_a_0 Int) (speed.res.inst_0_a_0 Bool)) Bool
    (and (= speed.usr.late_a_0 false) (= speed.res.abs_2_a_0 false) (= speed.res.abs_1_a_0 (and speed.usr.beacon_a_0 speed.usr.second_a_0)) (= speed.res.abs_0_a_0 0) (= speed.impl.usr.incr_a_0 (ite (and speed.usr.beacon_a_0 (not speed.usr.second_a_0)) 1 (ite (and speed.usr.second_a_0 (not speed.usr.beacon_a_0)) 2 0))) (let ((X1 speed.res.abs_3_a_0)) (and (= speed.usr.early_a_0 false) (__node_init_COUNTER_0 speed.res.abs_0_a_0 speed.impl.usr.incr_a_0 speed.res.abs_1_a_0 speed.res.abs_2_a_0 speed.res.abs_3_a_0 speed.res.inst_0_a_0) (<= 0 speed.res.abs_0_a_0 0) (<= 0 speed.impl.usr.incr_a_0 2) speed.res.init_flag_a_0))))
(define-fun __node_trans_speed_0 ((speed.usr.beacon_a_1 Bool) (speed.usr.second_a_1 Bool) (speed.usr.late_a_1 Bool) (speed.usr.early_a_1 Bool) (speed.res.init_flag_a_1 Bool) (speed.impl.usr.incr_a_1 Int) (speed.res.abs_0_a_1 Int) (speed.res.abs_1_a_1 Bool) (speed.res.abs_2_a_1 Bool) (speed.res.abs_3_a_1 Int) (speed.res.inst_0_a_1 Bool) (speed.usr.beacon_a_0 Bool) (speed.usr.second_a_0 Bool) (speed.usr.late_a_0 Bool) (speed.usr.early_a_0 Bool) (speed.res.init_flag_a_0 Bool) (speed.impl.usr.incr_a_0 Int) (speed.res.abs_0_a_0 Int) (speed.res.abs_1_a_0 Bool) (speed.res.abs_2_a_0 Bool) (speed.res.abs_3_a_0 Int) (speed.res.inst_0_a_0 Bool)) Bool
    (and (= speed.res.abs_2_a_1 false) (= speed.res.abs_1_a_1 (and speed.usr.beacon_a_1 speed.usr.second_a_1)) (= speed.res.abs_0_a_1 0) (= speed.impl.usr.incr_a_1 (ite (and speed.usr.beacon_a_1 (not speed.usr.second_a_1)) 1 (ite (and speed.usr.second_a_1 (not speed.usr.beacon_a_1)) 2 0))) (let ((X1 speed.res.abs_3_a_1)) (and (= speed.usr.late_a_1 (ite speed.usr.late_a_0 (< X1 0) (<= X1 (- 10)))) (= speed.usr.early_a_1 (ite speed.usr.early_a_0 (> X1 0) (>= X1 10))) (__node_trans_COUNTER_0 speed.res.abs_0_a_1 speed.impl.usr.incr_a_1 speed.res.abs_1_a_1 speed.res.abs_2_a_1 speed.res.abs_3_a_1 speed.res.inst_0_a_1 speed.res.abs_0_a_0 speed.impl.usr.incr_a_0 speed.res.abs_1_a_0 speed.res.abs_2_a_0 speed.res.abs_3_a_0 speed.res.inst_0_a_0) (<= 0 speed.res.abs_0_a_1 0) (<= 0 speed.impl.usr.incr_a_1 2) (not speed.res.init_flag_a_1)))))
(define-fun __node_init_top_0 ((top.usr.beacon_a_0 Bool) (top.usr.second_a_0 Bool) (top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.impl.usr.early_a_0 Bool) (top.res.abs_0_a_0 Bool) (top.res.abs_1_a_0 Bool) (top.res.inst_6_a_0 Bool) (top.res.inst_5_a_0 Int) (top.res.inst_4_a_0 Int) (top.res.inst_3_a_0 Bool) (top.res.inst_2_a_0 Bool) (top.res.inst_1_a_0 Int) (top.res.inst_0_a_0 Bool)) Bool
    (and (= top.usr.OK_a_0 true) (let ((X1 top.res.abs_0_a_0)) (and (= top.impl.usr.early_a_0 top.res.abs_1_a_0) (__node_init_speed_0 top.usr.beacon_a_0 top.usr.second_a_0 top.res.abs_0_a_0 top.res.abs_1_a_0 top.res.inst_6_a_0 top.res.inst_5_a_0 top.res.inst_4_a_0 top.res.inst_3_a_0 top.res.inst_2_a_0 top.res.inst_1_a_0 top.res.inst_0_a_0) top.res.init_flag_a_0))))
(define-fun __node_trans_top_0 ((top.usr.beacon_a_1 Bool) (top.usr.second_a_1 Bool) (top.usr.OK_a_1 Bool) (top.res.init_flag_a_1 Bool) (top.impl.usr.early_a_1 Bool) (top.res.abs_0_a_1 Bool) (top.res.abs_1_a_1 Bool) (top.res.inst_6_a_1 Bool) (top.res.inst_5_a_1 Int) (top.res.inst_4_a_1 Int) (top.res.inst_3_a_1 Bool) (top.res.inst_2_a_1 Bool) (top.res.inst_1_a_1 Int) (top.res.inst_0_a_1 Bool) (top.usr.beacon_a_0 Bool) (top.usr.second_a_0 Bool) (top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.impl.usr.early_a_0 Bool) (top.res.abs_0_a_0 Bool) (top.res.abs_1_a_0 Bool) (top.res.inst_6_a_0 Bool) (top.res.inst_5_a_0 Int) (top.res.inst_4_a_0 Int) (top.res.inst_3_a_0 Bool) (top.res.inst_2_a_0 Bool) (top.res.inst_1_a_0 Int) (top.res.inst_0_a_0 Bool)) Bool
    (let ((X1 top.res.abs_0_a_1)) (and (= top.usr.OK_a_1 (and (not top.impl.usr.early_a_0) (not X1))) (= top.impl.usr.early_a_1 top.res.abs_1_a_1) (__node_trans_speed_0 top.usr.beacon_a_1 top.usr.second_a_1 top.res.abs_0_a_1 top.res.abs_1_a_1 top.res.inst_6_a_1 top.res.inst_5_a_1 top.res.inst_4_a_1 top.res.inst_3_a_1 top.res.inst_2_a_1 top.res.inst_1_a_1 top.res.inst_0_a_1 top.usr.beacon_a_0 top.usr.second_a_0 top.res.abs_0_a_0 top.res.abs_1_a_0 top.res.inst_6_a_0 top.res.inst_5_a_0 top.res.inst_4_a_0 top.res.inst_3_a_0 top.res.inst_2_a_0 top.res.inst_1_a_0 top.res.inst_0_a_0) (not top.res.init_flag_a_1))))
(synth-inv str_invariant ((top.usr.beacon Bool) (top.usr.second Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.early Bool) (top.res.abs_0 Bool) (top.res.abs_1 Bool) (top.res.inst_6 Bool) (top.res.inst_5 Int) (top.res.inst_4 Int) (top.res.inst_3 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Int) (top.res.inst_0 Bool)))

(define-fun init ((top.usr.beacon Bool) (top.usr.second Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.early Bool) (top.res.abs_0 Bool) (top.res.abs_1 Bool) (top.res.inst_6 Bool) (top.res.inst_5 Int) (top.res.inst_4 Int) (top.res.inst_3 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Int) (top.res.inst_0 Bool)) Bool
    (and (= top.usr.OK true) (let ((X1 top.res.abs_0)) (and (= top.impl.usr.early top.res.abs_1) (__node_init_speed_0 top.usr.beacon top.usr.second top.res.abs_0 top.res.abs_1 top.res.inst_6 top.res.inst_5 top.res.inst_4 top.res.inst_3 top.res.inst_2 top.res.inst_1 top.res.inst_0) top.res.init_flag))))
(define-fun trans ((top.usr.beacon Bool) (top.usr.second Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.early Bool) (top.res.abs_0 Bool) (top.res.abs_1 Bool) (top.res.inst_6 Bool) (top.res.inst_5 Int) (top.res.inst_4 Int) (top.res.inst_3 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Int) (top.res.inst_0 Bool) (top.usr.beacon! Bool) (top.usr.second! Bool) (top.usr.OK! Bool) (top.res.init_flag! Bool) (top.impl.usr.early! Bool) (top.res.abs_0! Bool) (top.res.abs_1! Bool) (top.res.inst_6! Bool) (top.res.inst_5! Int) (top.res.inst_4! Int) (top.res.inst_3! Bool) (top.res.inst_2! Bool) (top.res.inst_1! Int) (top.res.inst_0! Bool)) Bool
    (let ((X1 top.res.abs_0!)) (and (= top.usr.OK! (and (not top.impl.usr.early) (not X1))) (= top.impl.usr.early! top.res.abs_1!) (__node_trans_speed_0 top.usr.beacon! top.usr.second! top.res.abs_0! top.res.abs_1! top.res.inst_6! top.res.inst_5! top.res.inst_4! top.res.inst_3! top.res.inst_2! top.res.inst_1! top.res.inst_0! top.usr.beacon top.usr.second top.res.abs_0 top.res.abs_1 top.res.inst_6 top.res.inst_5 top.res.inst_4 top.res.inst_3 top.res.inst_2 top.res.inst_1 top.res.inst_0) (not top.res.init_flag!))))
(define-fun prop ((top.usr.beacon Bool) (top.usr.second Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.early Bool) (top.res.abs_0 Bool) (top.res.abs_1 Bool) (top.res.inst_6 Bool) (top.res.inst_5 Int) (top.res.inst_4 Int) (top.res.inst_3 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Int) (top.res.inst_0 Bool)) Bool
    top.usr.OK)

(inv-constraint str_invariant init trans prop)

(check-synth)

