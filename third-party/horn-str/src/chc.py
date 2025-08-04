#!/bin/env python3

import argparse
import z3
import ismt
from enum import Enum
import lstar
import automata
from ice import ICELearner, MICELearner, ProductLearner
from datetime import datetime
from hornClause import *
from clauseTransform import *
from sfa_synthesis import SFAPassiveLearnerOverApprox
from reachabilityOracle import ReachabilityOracle

class CHCStrSolver(object):
    def __init__(self, fname=None,
            clauses=[],
            solver='ostrich',
            solver_mem='ostrich',
            group_oracles='no',
            debug=False,
            transducer=None,
            method_arguments=None,
            learner_debug=False):
        clauses = list(clauses)
        self.clauses = []
        self.solver = solver
        self.solver_mem = solver_mem
        self.debug = debug
        self.group_oracles = group_oracles
        self.transducer = transducer
        self.transform = Transform()
        self.method_arguments = method_arguments
        self.monadic = True
        self.linear = True
        self.params_num = 1
        self.learner_debug = learner_debug
        self.pad = "p"
        alpha = set()
        if fname:
            clauses += z3.parse_smt2_file(fname)
        for c in clauses:
            hc = HornClause(c, self)
            if hc.varin:
                if len(hc.varin) > 1:
                    self.monadic = False
                    self.params_num = max(self.params_num, len(hc.varin))

            if hc.varout:
                if len(hc.varout) > 1:
                    self.monadic = False
                    self.params_num = max(self.params_num, len(hc.varout))

            if len(hc.pre) > 1 or len(hc.post) > 1:
                self.linear = False
            # reduction for multiple predicates 
            if self.transducer == 'unification':
                hc = self.transform.unification_predicate_transformation(hc)
            alpha.update(hc.alpha)
            self.clauses.append(hc)

        if self.monadic:
            self.alpha = alpha
            self.universe = z3.Star(z3.Union(*list(z3.Re(c) for c in self.alpha)))
        else:
            if self.transducer == 'interleaving':
                self.alpha = alpha
                self.alpha.add(self.pad)
            elif self.transducer == 'concatenation':
                self.alpha = alpha
                self.alpha.add(self.pad)
            else:
                self.alpha = alpha
                self.alpha.add(self.pad)

            self.universe = z3.Star(z3.Union(*list(z3.Re(c) for c in self.alpha)))
            
        self.uninterpreted = set()

        for c in self.clauses:
            for p in c.uninterpreted:
                self.uninterpreted.add(p)
                

    def build_solver(self, mem=False):
        """Build a new SMT solver.
        If this will be used for membership queries (mem=True), another
        brand of solvers may be used.
        For example, z3 turns out to be faster at solving simple equations, but
        fails for larger one (appearing in an equivalence check).
        """
        s_name = self.solver_mem if mem else self.solver
        if s_name == 'z3':
            s = ismt.Z3(debug=self.debug)
        elif s_name == 'z3-alpha':
            s = ismt.Z3Alpha(debug=self.debug)
        elif s_name == 'z3-noodler':
            s = ismt.Z3Noodler(debug=self.debug, native_auto=False)
        elif s_name == 'cvc5':
            s = ismt.CVC5(debug=self.debug)
        elif s_name == 'ostrich':
            s = ismt.Ostrich(debug=self.debug, native_auto=True)
        elif s_name == 'ostrich-fwd':
            s = ismt.OstrichFWD(debug=self.debug, native_auto=True)
        elif s_name == 'ostrich-fwd-regex':
            s = ismt.OstrichFWD(debug=self.debug, native_auto=False)
        elif s_name == 'ostrich-regex':
            s = ismt.Ostrich(debug=self.debug, native_auto=False)
        else:
            raise NotImplementedError(f"Unknown solver {self.solver}")
        return s

    def build_equiv_oracle_list(self, symbolic=False, multiple=False, num = None):
        if self.linear and self.monadic:
            if self.group_oracles == 'no': 
                if symbolic:
                    return [(f"clause n°{i} {c.hc_type}", self.build_equiv_check_linear([c], c.hc_type, symbolic= True))\
                        for (i,c) in enumerate(self.clauses)]
                else:
                    return [(f"clause n°{i} {c.hc_type}", self.build_equiv_check_linear([c], c.hc_type))\
                        for (i,c) in enumerate(self.clauses)]
            elif self.group_oracles == 'by-type':
                r = []
                for t in HornClauseType:
                    label = f"{t.name} clauses"
                    l = [c for c in self.clauses if c.hc_type == t]
                    if symbolic:
                        r.append((label, self.build_equiv_check_linear(l, symbolic=True)))
                    else:
                        r.append((label, self.build_equiv_check_linear(l)))
                return r
            elif self.group_oracles == 'all':
                if symbolic:
                    return [('all', self.build_equiv_check_linear(self.clauses, symbolic=True))]
                else:
                    return [('all', self.build_equiv_check_linear(self.clauses))]
            else:
                raise NotImplementedError(f"Unsupported oracle grouping {self.group_oracles}")
        elif self.linear and not self.monadic:
            # body contains only one predicate with more than one parameter
            if self.group_oracles == 'no': 
                if symbolic:
                    return [(f"clause n°{i} {c.hc_type}", self.build_equiv_check_linear([c], c.hc_type, symbolic=True))\
                    for (i,c) in enumerate(self.clauses)]
                else:
                    return [(f"clause n°{i} {c.hc_type}", self.build_equiv_check_linear([c], c.hc_type))\
                        for (i,c) in enumerate(self.clauses)]
            elif self.group_oracles == 'by-type':
                r = []
                for t in HornClauseType:
                    label = f"{t.name} clauses"
                    l = [c for c in self.clauses if c.hc_type == t]
                    r.append((label, self.build_equiv_check_linear(l)))
                return r
            elif self.group_oracles == 'all':
                return [('all', self.build_equiv_check_linear(self.clauses))]
            else:
                raise NotImplementedError(f"Unsupported oracle grouping {self.group_oracles}")
        else:
            if self.group_oracles == 'no': 
                if symbolic:
                    return [(f"clause n°{i} {c.hc_type}", self.build_equiv_check_for_symbolic([c], c.hc_type))\
                        for (i,c) in enumerate(self.clauses)]
                elif multiple:
                    return [(f"clause n°{i} {c.hc_type}", self.build_equiv_check_for_nonlinear([c], c.hc_type, num=num))\
                        for (i,c) in enumerate(self.clauses)]
                else:
                    return [(f"clause n°{i} {c.hc_type}", self.build_equiv_check([c], c.hc_type))\
                        for (i,c) in enumerate(self.clauses)]
            elif self.group_oracles == 'by-type':
                r = []
                for t in HornClauseType:
                    label = f"{t.name} clauses"
                    l = [c for c in self.clauses if c.hc_type == t]
                    if symbolic:
                        r.append((label, self.build_equiv_check_for_symbolic(l)))
                    else:
                        r.append((label, self.build_equiv_check(l)))
                return r
            elif self.group_oracles == 'all':
                if symbolic:
                    return [('all', self.build_equiv_check_for_symbolic(self.clauses))]
                else:
                    return [('all', self.build_equiv_check(self.clauses))]
            else:
                raise NotImplementedError(f"Unsupported oracle grouping {self.group_oracles}")

    
    def build_equiv_check_for_nonlinear(self, clauses=None, hc_type=None, num = None):
        """Build an equivalence check for all clauses simultaneously"""
        if clauses is None:
            clauses = self.clauses
        solver = self.build_solver()
        varins = [z3.String(f"varin{i}") for i in range(num)]
        varouts = [z3.String(f"varout{i}") for i in range(num)]
        isin, isout = z3.Bools("isin isout")
        for i in range(num):
            solver.add(z3.InRe(varins[i], self.universe))
            solver.add(z3.InRe(varouts[i], self.universe))
        dij = [] # list of alternatives
        for (i,c) in enumerate(clauses):
            form = [c.condition]
            if c.varin is not None:
                for i in range(num):
                    form.append(z3.String(f"cl_varin{i}") == varins[i])
                form.append(isin)
            else:
                form.append(z3.Not(isin))
            if c.varout is not None:
                for i in range(num):
                    form.append(z3.String(f"cl_varout{i}") == varouts[i])
                form.append(isout)
            else:
                form.append(z3.Not(isout))
            dij.append(z3.And(form))
        solver.add(z3.Or(dij))
        def equivalence(autos):
            nonlocal solver
            with solver.context():
                if hc_type is HornClauseType.BLOCK:
                    for i in range(len(autos)):
                        solver.add_word_membership(varins[i], autos[i], flag=isin)
                elif hc_type is HornClauseType.INIT:
                    for i in range(len(autos)):
                        solver.add_word_membership(varouts[i], autos[i], negate=True, flag=isout)
                else:
                    for i in range(len(autos)):
                        solver.add_word_membership(varins[i], autos[i], flag=isin)
                        solver.add_word_membership(varouts[i], autos[i], negate=True, flag=isout)
                res = solver.check()
                if res == z3.unknown:
                    raise NotImplementedError("Cannot check equivalence")
                if res == z3.unsat:
                    return None
                # Build a counterexample
                m = solver.model()
                res_cex = dict()
                for i in range(num):
                    res_cex[i] = [None, None]
                if bool(m[isin]):
                    for i in range(num):
                        res_cex[i][0] = m[varins[i]].as_string()
                if bool(m[isout]):
                    for i in range(num):
                        res_cex[i][1] = m[varouts[i]].as_string()
                res = []
                for k, v in res_cex.items():
                    cex1 = v[0]
                    cex2 = v[1]
                    if cex1 is not None and cex2 is not None:
                        tmp = (cex1, cex2)
                        res.append(tmp)
                    elif cex1 is not None:
                        res.append(cex1)
                    elif cex2 is not None:
                        res.append(cex2)
                return res
         
        return equivalence

    def build_equiv_check_linear(self, clauses=None, hc_type=None, symbolic = False):
        """Build an equivalence check for all clauses simultaneously"""
        if clauses is None:
            clauses = self.clauses
        solver = self.build_solver()
        if self.transducer == 'interleaving':
            for (i,c) in enumerate(clauses):
                solver.add_interleaving_transducer(True, c.varin)
                solver.add_interleaving_transducer(False, c.varout)
        elif self.transducer == 'concatenation':
            for (i,c) in enumerate(clauses):
                solver.add_concat_transducer(True, c.varin, self.pad, universal=True) 
                solver.add_concat_transducer(False, c.varout, self.pad, universal=True)
        varin, varout = z3.Strings("varin varout")
        solver.add(z3.InRe(varout, self.universe))
        solver.add(z3.InRe(varin, self.universe))
        isin, isout = z3.Bools("isin isout")
        dij = [] # list of alternatives
        for (i,c) in enumerate(clauses):
            form = [c.condition]                
            if c.varin is not None:
                if self.monadic:
                    form.append(c.varin[0] == varin)
                else:
                    if self.transducer == 'interleaving':
                        for inx in range(len(c.varin)):
                            self.varinExtract0 = z3.Function(f"extractVarin{inx}", z3.StringSort(), z3.StringSort(), z3.BoolSort())
                            form.append(self.varinExtract0(varin, c.varin[inx]))
                    elif self.transducer == 'concatenation':
                        for inx in range(len(c.varin)):
                            solver.declare_var(c.varin[inx])
                            self.varinExtract0 = z3.Function(f"extractVarin{inx}", z3.StringSort(), z3.StringSort(), z3.BoolSort())
                            form.append(self.varinExtract0(varin, c.varin[inx]))
                    else:
                        # concat each item in varin with self.pad
                        for i in range(len(c.varin)):
                            if i > 0:
                                tmp = tmp + self.pad + c.varin[i]
                            else:
                                tmp = c.varin[i]
                        form.append(tmp == varin)
                form.append(isin)
            else:
                form.append(z3.Not(isin))
            if c.varout is not None:
                if self.monadic:
                    form.append(c.varout[0] == varout)
                if self.transducer == 'interleaving':
                    for inx in range(len(c.varout)):
                        solver.declare_var(c.varout[inx])
                        self.varinExtract0 = z3.Function(f"extractVarout{inx}", z3.StringSort(), z3.StringSort(), z3.BoolSort())
                        form.append(self.varinExtract0(varout, c.varout[inx]))
                elif self.transducer == 'concatenation':
                    for inx in range(len(c.varout)):
                        solver.declare_var(c.varout[inx])
                        self.varinExtract0 = z3.Function(f"extractVarout{inx}", z3.StringSort(), z3.StringSort(), z3.BoolSort())
                        form.append(self.varinExtract0(varout, c.varout[inx]))
                else:
                    for i in range(len(c.varout)):
                            if i > 0:
                                tmp = tmp + self.pad + c.varout[i]
                            else:
                                tmp = c.varout[i]
                    form.append(tmp == varout)
                form.append(isout)
            else:
                form.append(z3.Not(isout))
            dij.append(z3.And(form))
        solver.add(z3.Or(dij))
        def equivalence(auto):
            nonlocal solver
            with solver.context():
                if hc_type is HornClauseType.BLOCK:
                    solver.add_word_membership(varin, auto, flag=isin, linear = False, symbol = symbolic)
                elif hc_type is HornClauseType.INIT:
                    solver.add_word_membership(varout, auto, negate=True, flag=isout, linear = False, symbol = symbolic)
                else:
                    solver.add_word_membership(varin, auto, flag=isin, linear = False, symbol = symbolic)
                    solver.add_word_membership(varout, auto, negate=True, flag=isout, linear = False, symbol = symbolic)
                res = solver.check()
                if res == z3.unknown:
                    raise NotImplementedError("Cannot check equivalence")
                if res == z3.unsat:
                    return None
                # Build a counterexample
                m = solver.model()
                cex1 = cex2 = None
                if bool(m[isin]):
                    # if self.transducer == 'interleaving':
                    #     cex1 = self.interleave_words([m[i].as_string() for i in c.varin])
                    # else:
                    cex1 = m[varin].as_string()
                if bool(m[isout]):
                    # if self.transducer == 'interleaving':
                    #     cex2 = self.interleave_words([m[i].as_string() for i in c.varout])
                    # else:
                    cex2 = m[varout].as_string()
                if cex1 is not None and cex2 is not None: # inductive cex
                    return (cex1, cex2)
                if cex1 is not None:
                    return cex1
                else:
                    return cex2
        return equivalence
    
    def interleave_words(self, words):
        result = []
        max_len = max(len(w) for w in words)
        for i in range(max_len):
            for w in words:
                if i < len(w):
                    result.append(w[i])
                else:
                    result.append(self.pad)
        return ''.join(result)

    def get_init_clauses(self):
        c_init = [c for c in self.clauses if c.hc_type == HornClauseType.INIT]
        return c_init

    def get_blocking_clauses(self):
        c_bad = [c for c in self.clauses if c.hc_type == HornClauseType.BLOCK]
        return c_bad

    def get_inductive_clauses(self):
        c_tr = [c for c in self.clauses if c.hc_type == HornClauseType.INDUCTIVE]
        return c_tr 

    def check_sat_based(self, solver = 'z3', debug = False, name = None):
        """Check satifiability, using SAT-based RMC with length-preserving
        clauses only""" 
        start_time = datetime.now()
        # Two oracles
        c_init = self.get_init_clauses()
        print(len(c_init))
        c_bad = self.get_blocking_clauses()
        print(len(c_bad))
        c_tr = self.get_inductive_clauses()
        print(len(c_tr))
        print("reachable start")
        print(self.alpha)
        if self.linear:
            if self.monadic:
                l = ICELearner(self.alpha, solver = solver, debug= self.learner_debug)
            else:
                if self.transducer == 'interleaving':
                    l = ICELearner(self.alpha, solver = solver, debug = self.learner_debug)
                elif self.transducer == 'concatenation':
                    print(self.alpha)
                    l = ICELearner(self.alpha, solver = solver, debug= self.learner_debug)
                else:
                    l = ICELearner(self.alpha, solver = solver, debug= self.learner_debug)
            equiv_functions = self.build_equiv_oracle_list()
            refined = True
            i = 0
            while (refined):
                refined = False
                m = l.get_hyp()
                i += 1
                m.show_graphviz(f"{i}")
                for (equiv_name,f) in equiv_functions:
                    # print(f"Checking equivalence for {equiv_name}")
                    # if refined:
                        # m = l.get_hyp()
                    cex = f(m)
                    if cex is None:
                        continue
                    if type(cex) == tuple:
                        print(f"Tuple: {cex}")
                        l.solve_inductive_pair(cex)
                    elif not m.membership(cex):
                        print(f"Positive for l: {cex}")
                        l.solve_pos_ex(cex)
                    elif m.membership(cex):
                        print(f"Negative for l: {cex}")
                        l.solve_neg_ex(cex)
                    refined = True
                    break
                else:
                    auto = (l.get_hyp())
                    time = (f"{datetime.now() - start_time}")
                    size = auto.get_nb_states()
                    print(f"-----------------------------------------\ntime:{time}\nsize:{size}\npos: {l._pos}, neg: {l._neg}, ind: {l._pair}")
                    auto.show_graphviz(f"ICE,time:{time}\nsize:{size}")
        else:
            if self.params_num == 1:
                l = ProductLearner(self.alpha, solver = solver, invs_num=self.invs_num)
            equiv_functions = self.build_equiv_oracle_list(multiple=True, symbolic=False, num=self.invs_num)
            refined = True
            while (refined):
                refined = False 
                for (equiv_name,f) in equiv_functions:
                    # print(f"Checking equivalence for {equiv_name}")
                    # print(f"pos: {l.pos}, neg: {l.neg}, ind: {l.pair}")
                    ms = l.get_hyp()
                    cex = f(ms)
                    if cex is None:
                        continue
                    for i in range(self.invs_num):
                        if type(cex[i]) == tuple:
                            # print(f"Tuple: {cex[i]}")
                            l.solve_inductive_pair(cex[i], i)
                        elif not ms[i].membership(cex[i]):
                            # print(f"Positive for l{i}: {cex[i]}")
                            l.solve_pos_ex(cex[i], i)
                        elif ms[i].membership(cex[i]):
                            # print(f"Negative for l{i}: {cex[i]}")
                            l.solve_neg_ex(cex[i], i)
                    refined = True
                    break
                else:
                    auto = (l.get_hyp())
                    time = (f"{datetime.now() - start_time}")
                    # size = auto.get_nb_states()
                    print(f"-----------------------------------------\ntime:{time}\npos: {l.pos}, neg: {l.neg}, ind: {l.pair}")
                    # print(auto.to_regex(regex.Z3Builder()))
                    # auto.show(f"ICE,time:{time}\nsize:{size}")

    def check_sfa_passive_learning(self, greatest=False, approx: int=None):
        # initialisation
        start_time = datetime.now()
        # Two oracles
        c_init = self.get_init_clauses()
        print(len(c_init))
        c_bad = self.get_blocking_clauses()
        print(len(c_bad))
        c_tr = self.get_inductive_clauses()
        print(len(c_tr))
        # reachable = ReachabilityOracle(
        #     (c.build_set_oracle() for c in c_init),
        #     (c.build_transition_oracle() for c in c_tr),
        #     approx=approx,
        # )
        # unsafe = ReachabilityOracle(
        #     (c.build_set_oracle() for c in c_bad),
        #     (c.build_transition_oracle(post=False) for c in c_tr),
        #     approx=approx,
        # )

        # Check that it's length preserving
        if approx is None:
            for c in self.clauses:
                if c.hc_type != HornClauseType.INDUCTIVE:
                    continue
                # if not c.is_length_preserving():
                #     raise NotImplementedError(f"Clause {c} is not length preserving, use another method or -a")
        print("reachable start")
        equiv_functions = self.build_equiv_oracle_list(symbolic=True)
        learner = SFAPassiveLearnerOverApprox([], [], [], setting=self.method_arguments)
        refined = True
        while (refined):
            refined = False
            sfa = learner.run()
            for (equiv_name, f) in equiv_functions:
                if refined:
                    sfa = learner.run()
                cex = f(sfa)
                print(f"Checking equivalence for {equiv_name}")
                print("Positive:", learner.positive_examples)
                print("Negative:", learner.negative_examples)

                if cex is None:
                    continue
                print(f"Got CEX {repr(cex)}")
                if type(cex) == tuple:                    
                    print(f"Tuple: {cex}")
                    learner.solve_ind_ex(cex)
                elif not sfa.accepts(cex):
                    learner.solve_pos_ex(cex)
                elif sfa.accepts(cex):
                    learner.solve_neg_ex(cex)
                refined = True
                break

            else:
                print("pos:", learner.positive_examples)
                print("neg:", learner.negative_examples)
                auto = (learner.run())
                time = (f"{datetime.now() - start_time}")
                size = auto.get_nb_states()
                print(f"time:{time}\nsize:{size}")
                print("learner calls:{}".format(learner.iteration))
                #print(auto.accepts("T=0101"))
                #auto.show("test")
        return None


    def check_lstar_based(self, greatest=True, approx: int=None):
        """Check satifiability, using L*-based RMC with length-preserving
        clauses only.
        This is based on membership oracles for reachable and unsafe states.
        If a state is nor reachable nor bad, a default answer has to be given:
        if True is returned, the learning process aims at learning the greatest
        inductive set, namely the safety set.
        If False is returned, the process learns the smallest inductive set.
        Similar decisions have to be taken for inductive counterexamples.

        approx: how much a transition can change the length of a word?
        If None, will refuse to deal with non-length preserving transitions.
        """
        start_time = datetime.now()
        l = lstar.LStar(self.alpha)
        # Two oracles
        c_init = self.get_init_clauses()
        print(len(c_init))
        c_bad = self.get_blocking_clauses()
        print(len(c_bad))
        c_tr = self.get_inductive_clauses()
        print(len(c_tr))
        # Check that it's length preserving
        if approx is None:
            for c in self.clauses:
                if c.hc_type != HornClauseType.INDUCTIVE:
                    continue
                if not c.is_length_preserving():
                    raise NotImplementedError(f"Clause {c} is not length preserving, use another method or -a")
        print("reachable start")
        reachable = ReachabilityOracle(
            (c.build_set_oracle() for c in c_init),
            (c.build_transition_oracle() for c in c_tr),
            approx=approx,
        )
        unsafe = ReachabilityOracle(
            (c.build_set_oracle() for c in c_bad),
            (c.build_transition_oracle(post=False) for c in c_tr),
            approx=approx,
        )
        equiv_functions = self.build_equiv_oracle_list()
        refined = True
        while refined:
            refined = False
            while l.get_membership_query() is not None:
                w = l.get_membership_query()
                # print("Query %r" % w)
                w_reach = reachable.query(w)
                w_unsafe = unsafe.query(w)
                w_answer = w_reach
                if w_reach and w_unsafe:
                    print(f"{w} is both reachable and unsafe")
                    return False
                elif not w_reach and not w_unsafe:
                    # blury area
                    w_answer = greatest
                # print(f"-> reach: {w_reach}, unsafe: {w_unsafe}, answer: {w_answer}")
                l.answer_membership_query(w_answer)
            for (equiv_name,f) in equiv_functions:
                m = l.get_hypothesis()
                cex = f(m)
                if cex is None:
                    continue
                # print(f"Got CEX {repr(cex)}")
                if type(cex) == tuple:
                    print(f"Tuple: {cex}")
                    w_reach = reachable.query(cex[0])
                    w_unsafe = unsafe.query(cex[1])
                    # print(f"  (R,U) = ({w_reach}, {w_unsafe})")
                    # print(f"membership: ({l.get_hypothesis().membership(cex[0])}, {l.get_hypothesis().membership(cex[1])})")
                    if w_reach and w_unsafe:
                        # print(f"init->{cex[0]}->{cex[1]}->bad")
                        return False
                    if w_reach:
                        cex = cex[1]
                    elif w_unsafe:
                        cex = cex[0]
                    else: # arbitrary choice here
                        # print(f"Make the inductive choice here {cex}")
                        cex = cex[1] if greatest else cex[0]
                l.feed_cex(cex)
                refined = True
                break
            else:
                auto = (l.get_hypothesis())
                time = (f"{datetime.now() - start_time}")
                size = auto.get_nb_states()
                print(f"time:{time}\nsize:{size}")
        return None
