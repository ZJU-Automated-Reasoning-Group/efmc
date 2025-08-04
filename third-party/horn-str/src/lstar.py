#!/bin/env python3

import learner
import automata
import itertools
from enum import Enum

class State(Enum):
    MEMBERSHIP = 1
    EQUIVALENCE = 2
    CEX_ANALYSIS = 3

class LStar(learner.Learner):
    """L* naive algo, but with binary cex refinement"""

    # empty word, could be "" or ()
    _empty = ""
    
    _hyp = None
    def __init__(self, alpha):
        """Alpha is an alphabet. Should be an iterable of words.
        Here a word is anything iterable that can be concatenated with +
        """

        if all(type(x) == str for x in alpha):
            self._empty = ""
        elif all(type(x) == tuple for x in alpha):
            self._empty = ()
        else:
            raise TypeError("Not all letters from alphabet of same type")

        self.alpha = alpha

        # observation table, for each word, an output value
        self.obs = {}
        self.prefixes = []
        self.suffixes = [self._empty]

        self.state = State.MEMBERSHIP

        self.membership_queries = set()
        self._add_prefix(self._empty)
    

    def get_membership_query(self):
        """Get a mem query"""
        if self.state == State.MEMBERSHIP:
            return next(iter(self.membership_queries))
        elif self.state == State.CEX_ANALYSIS:
            return next(iter(self.membership_queries))
        elif self.state == State.EQUIVALENCE:
            return None

    def get_hypothesis(self):
        return self._hyp

    def answer_membership_query(self, output, word=None):
        if word is None:
            word = self.get_membership_query()
        self.obs[word] = output
        self.membership_queries.remove(word)
        if self.state == State.MEMBERSHIP and not self.membership_queries:
            self._build_hyp()
        elif self.state == State.CEX_ANALYSIS:
            self._next_mem()
    
    _cex_analysis = None
    def feed_cex(self, cex):
        assert(self.state == State.EQUIVALENCE)
        self.state = State.CEX_ANALYSIS
        self._cex_analysis = self._proc_cex(cex)
        self._next_mem()

    def _next_mem(self):
        while not self.membership_queries:
            try:
                next(self._cex_analysis)
            except StopIteration:
                self._cex_analysis = None

    def all_prefixes(self, word):
        if word != self._empty:
            return [word[:i] for i in range(1, len(word) + 1)]
        else:
            return [self._empty]
    
    def _add_prefix(self, w):
        all_pref = self.all_prefixes(w)
        new_prefixes = []
        for i in all_pref:
            if i not in self.prefixes:
                new_prefixes.append(i)
                self.prefixes.append(i)
        for p in new_prefixes:
            for x in itertools.chain([self._empty], self.alpha):
                for s in self.suffixes:
                    if p + x + s not in self.obs:
                        self.membership_queries.add(p+x+s)
        self._check()

    def _add_suffix(self, w):
        assert(w not in self.suffixes)
        self.suffixes.append(w)
        for p in self.prefixes:
            for x in itertools.chain([self._empty], self.alpha):
                if p+x+w not in self.obs:
                    self.membership_queries.add(p+x+w)
        self._check()

    def _check(self):
        err = False
        for p in self.prefixes:
            for x in itertools.chain([self._empty], self.alpha):
                for s in self.suffixes:
                    w = p + x + s
                    if w not in self.obs and w not in self.membership_queries:
                        print(f"{w} = {p}+{x}+{s} not in obs nor planned")
                        err = True
        if err:
            raise AssertionError
    
    def raw(self, p):
        return tuple(self.obs[p + s] for s in self.suffixes)
    
    def consistent(self):
        """
        checks if the observation table is consistent
        """
        matchingpairs = [(p1, p2) for p1 in self.prefixes for p2 in self.prefixes
                         if p1 != p2 and self.raw(p1) == self.raw(p2)]
        suffixext = [(a, s) for a in self.alpha for s in self.suffixes]
        for p1,p2 in matchingpairs:
            for a, s in suffixext:
                if self.obs(p1+a+s) != self.obs(p2+a+s):
                        return False, (p1, p2), (a + s)
        return True, None, None
    
    def _build_hyp(self):
        """Attempts to build an hypothesis, or add new prefixes"""
        # for a given vector of outputs (one per suffix), to a given prefix
        vect = {}
        for p in self.prefixes:
            vect[tuple(self.obs[p + s] for s in self.suffixes)] = p
        
        missing = {}
        tab = {}
        for p in self.prefixes:
            tab[p] = {}
            for x in self.alpha:
                v = tuple(self.obs[p + x + s] for s in self.suffixes)
                if v in vect:
                    # closed 
                    tab[p][x] = vect[v]
                elif v not in missing:
                    missing[v] = p + x

        # consistent check, and add missing suffixes
        missing_suffixes = {}
        flag, _, w = self.consistent()
        if not flag:
            missing_suffixes.append(w)
        
        for p in missing.values():
            self._add_prefix(p)

        for p in missing_suffixes:
            self._add_suffix(p)

        if not missing and not missing_suffixes:
            acc = {p for p in self.prefixes if self.obs[p]}
            self._hyp = DFAFromTab(self.alpha, tab, self._empty, acc)
            self.state = State.EQUIVALENCE
            
        # It may happen we added prefixes, all queries have already been made
        if not self.membership_queries:
            self._build_hyp

    def _proc_cex(self, w):
        # Generator, add queries, then yield for waiting
        run = [self._empty]
        st = self._empty
        for x in w:
            st = self._hyp.tab[st][x]
            run.append(st)
        
        # Value of w in the hypothesis, which is wrong, so is the value
        value = self.obs[run[-1]]
        
        if w not in self.obs:
            self.membership_queries.add(w)
            yield
        real = self.obs[w]
        # We can (optionnaly) check that the value is different from the hyp:
        assert(real != value)

        # Binary search to find where value was obtained, instead (not value)
        i = 0; j = len(w)-1
        while j>i:
            # Invariant:
            # run[i] "≡" w[0:i]   (actually: o(run[i]·w[i:]) = o(w))
            # BUT
            # run[j+1] not(≡) w[0:j+1] because o(run[j+1]·w[j+1]) ≠ o(w)
            m = (i+j)//2 + 1
            before = run[m] + w[m:]
            if before not in self.obs:
                self.membership_queries.add(before)
                yield
            if self.obs[before] == real:
                i = m
            elif self.obs[before] != real:
                j = m-1

        # Now it's time for the next membership phase
        self.state = State.MEMBERSHIP
        self._add_suffix(w[i+1:])


class DFAFromTab(automata.NFA):
    def __init__(self, alphabet, tab, init, acc):
        super().__init__(alphabet)
        self.tab = tab
        self.init = init
        self.acc = acc

    def get_initial(self):
        yield self.init

    def get_succ(self, src, letter):
        yield self.tab[src][letter]

    def is_accepting(self, s):
        return s in self.acc



if __name__ == '__main__':
    target = automata.Kleene(automata.Disjunction(
        automata.SingleWordAcceptor("ab"),
        automata.SingleWordAcceptor("aab"),
    ))
    target = automata.Determinization(target)
    
    alpha = target.alphabet
    l = LStar(alpha)
    while True:
        while l.get_membership_query() is not None:
            w = l.get_membership_query()
            print("Query %r" % w)
            auto = automata.Intersection(target, automata.SingleWordAcceptor(w, alpha))
            answer = automata.find_word(auto) is not None
            print(" --> answer: %r" % (answer, ))
            l.answer_membership_query(answer)
        cex = automata.find_word(automata.Difference(target, l.get_hypothesis()))
        if cex is not None:
            cex = "".join(cex)
            print(" --> positive cex %r" % cex)
            l.feed_cex(cex)
            continue
        cex = automata.find_word(automata.Difference(l.get_hypothesis(), target))
        if cex is not None:
            cex = "".join(cex)
            print(" --> neg cex %r" % cex)
            l.feed_cex(cex)
            continue
        print("No cex found, terminating")
        l.get_hypothesis().show_graphviz("1")
        break
