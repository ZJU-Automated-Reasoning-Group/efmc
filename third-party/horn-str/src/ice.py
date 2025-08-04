#!/bin/env python3

import z3
from z3 import Bool, Or, And, Not, Implies
import automata
from ismt import Ostrich, Z3, Z3Noodler, CVC5
import utils
import itertools
import numpy as np
from automata import Intersection 



class ICELearner(object):
    def __init__(self, alphabet, n = 1, solver = "z3-noodler", debug = False):
        """An equivalence oracle is allowed to return None (if model
        learned), a counterexample, or a pair (u,v) such that if u is in L,
        then v should be too"""
        self.alphabet = alphabet

        # Current size of hypothesis auto
        self._n = n
        
        # Current z3 solver (for auto of size n)
        self._solver = None
        self.debug = debug

        self._pos = set()
        self._neg = set()
        self._pair = set()
        self._w = self._pos.union(self._neg)
        self.solver = solver
        self._build_form(solver)

    def _build_form(self, solver = "z3"):
        if self._pos.intersection(self._neg):
            raise ValueError("Positive and negative examples must be disjoint")
        if solver == "ostrich":
            self._solver = Ostrich(debug=self.debug)
        elif solver == "z3":
            self._solver = Z3(debug=self.debug)
        elif solver == "z3-noodler":
            self._solver = Z3Noodler(debug=self.debug)
        elif solver == "cvc5":
            self._solver = CVC5(debug=self.debug)

        states = range(self._n) # size of automaton 
        self._w = self._pos.union(self._neg)
        for i in self._pair:
            self._w.add(i[0])
            self._w.add(i[1])

        d = {} # delta: transition

        for p in states:
            for a in self.alphabet:
                for q in states:
                    d[(p, a, q)] = Bool(f"d_{p}_{a}_{q}")  # Transition function
        
        # Add constraints to ensure that the transition function is deterministic
        for p in states:
            for a in self.alphabet:
                self._solver.add(Or([d[(p, a, q)] for q in states]))  # At least one transition for each (p, a) pair
                for q in states:
                    for q_ in states:
                        if q != q_:
                            self._solver.add(Or(Not(d[(p, a, q)]), Not(d[(p, a, q_)])))  # Only one transition for each (p, a) pair

        # auxiliary formula w
        prefix = utils.prefix_set(self._w)

        for u in prefix:
            self._solver.add(Bool(f"acc_{u}") == Or([And(Bool(f"f_{q}"), Bool(f"x_{u}_{q}")) for q in states]))
            for q in states:
                for q_ in states:
                    if len(u)>0:
                        self._solver.add(Implies(And(Bool(f"x_{u[:-1]}_{q}"), d[(q, u[-1], q_)]), Bool(f"x_{u}_{q_}")))
                    if q != q_:
                        self._solver.add(Or(Not(Bool(f"x_{u}_{q}")), Not(Bool(f"x_{u}_{q_}")))) 

        #initial q0   
        self._solver.add(Bool(f"x__0"))

        # positive cex constraint
        for u in self._pos:
            for q in states:
                self._solver.add(Implies(Bool(f"x_{u}_{q}"),(Bool(f"f_{q}"))))

        # negative cex constraint
        for u in self._neg:
            for q in states:
                self._solver.add(Implies(Bool(f"x_{u}_{q}"), Not(Bool(f"f_{q}"))))

        # inductive cex constraint
        for (u,v) in self._pair:
            self._solver.add(Implies(Bool(f"acc_{u}"), Bool(f"acc_{v}")))
        
        
    def solve_pos_ex(self, cex):
        self._pos.add(cex) # insert the positive cex into pos set

        prefix = utils.prefix_set({cex})
        
        states = range(self._n)

        for u in prefix:
            self._solver.add(Bool(f"acc_{u}") == Or([And(Bool(f"f_{q}"), Bool(f"x_{u}_{q}")) for q in states]))
            for q in states:
                for q_ in states:
                    if len(u)>0:
                        self._solver.add(Implies(And(Bool(f"x_{u[:-1]}_{q}"), Bool(f"d_{q}_{u[-1]}_{q_}")), Bool(f"x_{u}_{q_}")))
                    if q != q_:
                        self._solver.add(Or(Not(Bool(f"x_{u}_{q}")), Not(Bool(f"x_{u}_{q_}")))) 

        for q in states:
            self._solver.add(Implies(Bool(f"x_{cex}_{q}"),(Bool(f"f_{q}"))))


    def solve_neg_ex(self, cex):
        self._neg.add(cex) # insert the negative cex into neg set

        prefix = utils.prefix_set({cex})
        states = range(self._n)
        for u in prefix:
            self._solver.add(Bool(f"acc_{u}") == Or([And(Bool(f"f_{q}"), Bool(f"x_{u}_{q}")) for q in states]))
            for q in states:
                for q_ in states:
                    if len(u)>0:
                        self._solver.add(Implies(And(Bool(f"x_{u[:-1]}_{q}"), Bool(f"d_{q}_{u[-1]}_{q_}")), Bool(f"x_{u}_{q_}")))
                    if q != q_:
                        self._solver.add(Or(Not(Bool(f"x_{u}_{q}")), Not(Bool(f"x_{u}_{q_}")))) 

        for q in states:
            self._solver.add(Implies(Bool(f"x_{cex}_{q}"), Not(Bool(f"f_{q}"))))

    def solve_inductive_pair(self, cex):
        self._pair.add(cex) # insert inductive cex into pair set 

        prefix = utils.prefix_set({cex[0], cex[1]}) 
        states = range(self._n)
        for u in prefix:
            self._solver.add(Bool(f"acc_{u}") == Or([And(Bool(f"f_{q}"), Bool(f"x_{u}_{q}")) for q in states]))
            for q in states:
                for q_ in states:
                    if len(u)>0:
                        self._solver.add(Implies(And(Bool(f"x_{u[:-1]}_{q}"), Bool(f"d_{q}_{u[-1]}_{q_}")), Bool(f"x_{u}_{q_}")))
                    if q != q_:
                        self._solver.add(Or(Not(Bool(f"x_{u}_{q}")), Not(Bool(f"x_{u}_{q_}")))) 

        self._solver.add(Implies(Bool(f"acc_{cex[0]}"), Bool(f"acc_{cex[1]}")))


    def get_hyp(self):
        while self._solver.check() == z3.unsat:
            print("increasing size: " + str(self._n + 1) )

            self._n += 1
            self._build_form(self.solver)
        model =  DFAModel(self.alphabet, self._solver.model(), self._n)
        
        return model


class ProductLearner(object):
    def __init__(self, alphabet, invs_num = 1, params_num = 1, solver = "z3-noodler"):
        self.alphabet = alphabet
        self._ns = [1 for _ in range(invs_num)]
        self.solver = solver
        if params_num != 1:
            self.learners = [MICELearner(alphabet, n, solver, params = params_num) for n in self._ns]
        else:
            self.learners = [ICELearner(alphabet, n, solver) for n in self._ns]
        self.pos = {i: set() for i in range(invs_num)}
        self.neg = {i: set() for i in range(invs_num)} 
        self.pair = {i: set() for i in range(invs_num)}
        for i in range(invs_num):
            self.learners[i]._pos = self.pos[i]
            self.learners[i]._neg = self.neg[i]
            self.learners[i]._pair = self.pair[i]

    def get_hyp(self):
        res = [learner._solver.check() for learner in self.learners]
        while z3.unsat in res:
            inx = res.index(z3.unsat)
            self._ns[inx] += 1
            self.learners[inx]._n = self._ns[inx]
            self.learners[inx]._build_form(self.solver)
            res = [learner._solver.check() for learner in self.learners]
        models = [learner._solver.model() for learner in self.learners]
        return [DFAModel(self.alphabet, models[i], self.learners[i]._n) for i in range(len(models))]

    def solve_pos_ex(self, cex, id):
        # print(f"solving pos {cex} in learner {id}")
        self.pos[id].add(cex)
        self.learners[id].solve_pos_ex(cex)

    def solve_neg_ex(self, cex, id):
        # print(f"solving neg {cex} in learner {id}")
        self.neg[id].add(cex)
        self.learners[id].solve_neg_ex(cex)
        
    
    def solve_inductive_pair(self, cex, id):
        # print(f"solving pair {cex} in learner {id}")
        self.pair[id].add(cex)
        self.learners[id].solve_inductive_pair(cex)
        
       
class DFAModel(automata.NFA):
    def __init__(self, alphabet, model, n):
        super().__init__(alphabet)
        self.model = model
        self.size = n
    
    def getNbStates(self):
        return self.size

    def get_succ(self, src, letter):
        for i in range(self.size):
            assert(Bool('d_{0}_{1}_{2}'.format(src, letter,i)) in self.model.keys())
            if self.model[Bool('d_{0}_{1}_{2}'.format(src, letter, i))]:
                yield i    
            
    def get_initial(self):
        yield 0

    def is_accepting(self, st):
        if Bool('f_%d' % st) not in self.model:
            return True
        return bool(self.model[Bool('f_%d' % st)])

 
class MICELearner(object):
    def __init__(self, alp1, pos= set(), neg= set(), pair = set(), n=1, solver="z3-noodler", pad = 'p', params = 1, debug = False):  
        """An ICE Learner that handles words in the form wa_wb where wa ∈ alp1* and wb ∈ alp2*
        
        Args:
            alp: First alphabet
            separator: Symbol separating words from alp1* and alp2* (default: "_")
            n: Initial size of hypothesis automaton
            solver: SMT solver to use
        """
        # Ensure alphabets are stored as tuples

        self._n = n
        
        # Current solver (for automata of size n)
        self._solver = None
        self._pos = pos
        self._neg = neg
        self._pair = pair
        self._w = self._pos.union(self._neg)
        self.solver = solver
        self.alphabet = alp1
        self.params = params
        self.debug = debug
        self._build_form(solver)

    
        
    def _build_form(self, solver="z3-noodler"):
        if solver == "ostrich":
            self._solver = Ostrich(debug=self.debug)
        elif solver == "z3":
            self._solver = Z3(debug=self.debug)
        elif solver == "z3-noodler":
            self._solver = Z3Noodler(debug=self.debug)
        elif solver == "cvc5":
            self._solver = CVC5(debug=self.debug)

        states = range(self._n)  # size of automaton 
        # Create the original set from positive and negative examples
        # Filter out elements from alphabet1
        self._w = self._pos.union(self._neg)
        for i in self._pair:
            self._w.add(i[0])
            self._w.add(i[1])

        d = {} # delta: transition

        for p in states:
            for a in self.alphabet:
                for q in states:
                    d[(p, a, q)] = Bool(f"d_{p}_{a}_{q}")  # Transition function
        
        # Add constraints to ensure that the transition function is deterministic
        for p in states:
            for a in self.alphabet:
                self._solver.add(Or([d[(p, a, q)] for q in states]))  # At least one transition for each (p, a) pair
                for q in states:
                    for q_ in states:
                        if q != q_:
                            self._solver.add(Or(Not(d[(p, a, q)]), Not(d[(p, a, q_)])))  # Only one transition for each (p, a) pair

        # auxiliary formula w
        prefix = utils.paired_prefix_set(self._w)
        for u in prefix:
            self._solver.add(Bool(f"acc_{u}") == Or([And(Bool(f"f_{q}"), Bool(f"x_{u}_{q}")) for q in states]))
            for q in states:
                for q_ in states:
                    if len(u)>1:
                        self._solver.add(Implies(And(Bool(f"x_{u[:-2]}_{q}"), Bool(f"d_{q}_{u[-2]}{u[-1]}_{q_}")), Bool(f"x_{u}_{q_}")))
                    if q != q_:
                        self._solver.add(Or(Not(Bool(f"x_{u}_{q}")), Not(Bool(f"x_{u}_{q_}")))) 

        #initial q0   
        self._solver.add(Bool(f"x__0"))

        # positive cex constraint
        for u in self._pos:
            for q in states:
                self._solver.add(Implies(Bool(f"x_{u}_{q}"),(Bool(f"f_{q}"))))

        # negative cex constraint
        for u in self._neg:
            for q in states:
                self._solver.add(Implies(Bool(f"x_{u}_{q}"), Not(Bool(f"f_{q}"))))

        # inductive cex constraint
        for (u,v) in self._pair:
            self._solver.add(Implies(Bool(f"acc_{u}"), Bool(f"acc_{v}")))
        
        
    def solve_pos_ex(self, cex):
        self._pos.add(cex) # insert the positive cex into pos set

        prefix = utils.paired_prefix_set({cex})
        
        states = range(self._n)

        for u in prefix:
            self._solver.add(Bool(f"acc_{u}") == Or([And(Bool(f"f_{q}"), Bool(f"x_{u}_{q}")) for q in states]))
            for q in states:
                for q_ in states:
                    if len(u)>1:
                        self._solver.add(Implies(And(Bool(f"x_{u[:-2]}_{q}"), Bool(f"d_{q}_{u[-2]}{u[-1]}_{q_}")), Bool(f"x_{u}_{q_}")))
                    if q != q_:
                        self._solver.add(Or(Not(Bool(f"x_{u}_{q}")), Not(Bool(f"x_{u}_{q_}")))) 

        for q in states:
            self._solver.add(Implies(Bool(f"x_{cex}_{q}"),(Bool(f"f_{q}"))))


    def solve_neg_ex(self, cex):
        self._neg.add(cex) # insert the negative cex into neg set

        prefix = utils.paired_prefix_set({cex})
        states = range(self._n)
        for u in prefix:
            self._solver.add(Bool(f"acc_{u}") == Or([And(Bool(f"f_{q}"), Bool(f"x_{u}_{q}")) for q in states]))
            for q in states:
                for q_ in states:
                    if len(u)>1:
                        self._solver.add(Implies(And(Bool(f"x_{u[:-2]}_{q}"), Bool(f"d_{q}_{u[-2]}{u[-1]}_{q_}")), Bool(f"x_{u}_{q_}")))
                    if q != q_:
                        self._solver.add(Or(Not(Bool(f"x_{u}_{q}")), Not(Bool(f"x_{u}_{q_}")))) 

        for q in states:
            self._solver.add(Implies(Bool(f"x_{cex}_{q}"), Not(Bool(f"f_{q}"))))

    def solve_inductive_pair(self, cex):
        self._pair.add(cex) # insert inductive cex into pair set 

        prefix = utils.paired_prefix_set({cex[0], cex[1]}) 
        states = range(self._n)
        for u in prefix:
            self._solver.add(Bool(f"acc_{u}") == Or([And(Bool(f"f_{q}"), Bool(f"x_{u}_{q}")) for q in states]))
            for q in states:
                for q_ in states:
                    if len(u)>0:
                        self._solver.add(Implies(And(Bool(f"x_{u[:-2]}_{q}"), Bool(f"d_{q}_{u[-2]}{u[-1]}_{q_}")), Bool(f"x_{u}_{q_}")))
                    if q != q_:
                        self._solver.add(Or(Not(Bool(f"x_{u}_{q}")), Not(Bool(f"x_{u}_{q_}")))) 

        self._solver.add(Implies(Bool(f"acc_{cex[0]}"), Bool(f"acc_{cex[1]}")))


    def get_hyp(self):
        self._build_form(self.solver)
        while self._solver.check() == z3.unsat:
            print("increasing size: " + str(self._n + 1) )
            self._n += 1
            self._build_form(self.solver)

        return DualDFAModel(self.alphabet, self._solver.model(), self._n, self.params)


class DualDFAModel(automata.NFA):
    def __init__(self, alphabet, model, n, params = 1):
        super().__init__(alphabet)
        self.model = model
        self.size = n
        self.params = params
    
    def getNbStates(self):
        return self.size

    def get_succ(self, src, letter):
        for i in range(self.size):
            assert(Bool('d_{0}_{1}_{2}'.format(src, letter,i)) in self.model.keys())
            if self.model[Bool('d_{0}_{1}_{2}'.format(src, letter, i))]:
                yield i    
            
    def get_initial(self):
        yield 0

    def is_accepting(self, st):
        if Bool('f_%d' % st) not in self.model:
            return True
        return bool(self.model[Bool('f_%d' % st)])
    
    def membership(self, word):
        """
        Check if the word (list of letters) is accepted.
        The word is expected to be in tuples of length self.params.
        """
        n = len(word) // self.params  # Number of tuples
        cur = set(self.get_initial())  # Start with the initial states
        for i in range(n):
            # Extract a tuple of self.params characters
            tuple_chars = ''.join(word[self.params * i:self.params * (i + 1)])
            next_states = set()
            for st in cur:
                next_states.update(self.get_succ(st, tuple_chars))  # Get successors for the tuple
            cur = next_states  # Update the current states

        # Check if any of the current states are accepting
        return any(self.is_accepting(st) for st in cur)

if __name__ == '__main__':
    # Example usage
    import regex

    learner = ICELearner(alphabet=['1', '2'], n=1, solver="z3-noodler", debug=True)
    learner.solve_pos_ex("1")
    learner.solve_neg_ex("2")
    m = {'T0':'1', 'B0':'2'}
    auto = learner.get_hyp(m)
    print(auto.to_regex(regex.Z3Builder()))
    auto.show("123")
    
    # print(hyp.membership("T1"))
    # print(hyp.membership("B0"))  # Should return True if accepted
    # print(hyp.membership("B0p0"))
    # # print(hyp.to_regex(regex.Z3Builder()))

