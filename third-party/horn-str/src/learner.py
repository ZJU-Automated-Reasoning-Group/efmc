#!/bin/env python3

from automata import NFA, TrivialA, MatrixNFA
import automata
import subprocess

class Learner(object):
    """A standard learner, with fork capabilities"""

    def __init__(self):
        raise NotImplementedError("abstract")

    def clone(self):
        """Clone (fork) current learner"""
        raise NotImplementedError()

    ## Membership Queries
    def get_membership_query(self):
        """Return the current element being queried for membership"""
        raise NotImplementedError()
    
    def answer_membership_query(self, answer):
        """Answer the query with True (in the set) or False (not in the set)"""
        raise NotImplementedError()

    ## Equivalence Queries
    def get_hypothesis(self):
        """Get current hypothesis (should always exists)"""
        raise NotImplementedError()

    def get_size(self):
        """Return size of current hypothesis, or a lower bound on the next
        one (if some membership queries are still unanswered"""
        raise NotImplementedError()
    
    def feed_cex(self, cex):
        """Provide a counterexample to current hypothesis, to the learner"""
        raise NotImplementedError()

    ## Useful method for manual testing
    def interactive(self):
        print("Interactive mode, ctrl+c to interupt")
        while True:
            while self.get_membership_query() is not None:
                print(f"Mem: {repr(self.get_membership_query())} ?")
                self.answer_membership_query(self._ask_output())
            print("An hypothesis is ready:")
            print("Counterexample ? (close window to validate)")
            self.get_hypothesis().show()
            self.feed_cex(input())

    def _ask_output(self):
        while True:
            try:
                return bool(int(input()))
            except ValueError:
                print("Wrong format, expected 0 or 1")


class JavaLStar(Learner):
    def __init__(self, alpha):
        PATH='../unsure_oracle/unsure_oracle.jar'
        self.proc = subprocess.Popen(['java', '-jar', PATH],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )
        self.alpha = alpha
        self.is_membership = False
        self.queried = None
        self.send("d %s" % "".join(alpha))
        self.read_question_type()

    def read_question_type(self):
        while True:
            l = self.proc.stdout.readline().strip()
            if l == b'm':
                self.is_membership = True
                return
            elif l == b'e':
                self.is_membership = False
                return
            else:
                print("Read garbage: %r" % l)
    
    def send(self, s):
        self.proc.stdin.write(s.encode() + b'\n')
        self.proc.stdin.flush()

    def get_membership_query(self):
        assert(self.is_membership)
        if self.queried is None:
            self.send('w')
            while True:
                l = self.proc.stdout.readline().strip()
                self.queried = l.strip().decode()
                break
        return self.queried

    def answer_membership_query(self, a):
        self.send("a %d" % a)
        self.queried = None
        self.read_question_type()
    
    def get_hypothesis(self):
        if self.is_membership:
            return None
        self.send('s')
        n = int(self.proc.stdout.readline().strip())
        init = [0]
        mat = []
        # TODO: caveat: for initial states, one cannot tell if accepting or
        #not
        acc = []
        for i in range(n):
            d = {}
            mat.append(d)
            for l in self.alpha:
                self.send('h %d %s' % (i,l))
                dst,b = self.proc.stdout.readline().strip().split(b' ',1)
                dst = int(dst)
                d[l] = [dst]
                if b == b'1':
                    acc.append(dst)
        return MatrixNFA(init, acc, mat)

    def feed_cex(self, word):
        self.send('a %s' % "".join(word))
        self.read_question_type()

class DummyLearner(Learner):
    def __init__(self, result):
        self.result = result

    def get_membership_query(self):
        raise Exception("No membership query yet")

    def answer_membership_query(self):
        raise Exception("No")

    def get_hypothesis(self):
        return self.result

    def feed_cex(self, cex):
        pass
    
class LStar(Learner):
    """Naive L* algorithm"""

    # empty word, could be "" or ()
    _empty = ""

    # Last required membership query
    _last_meq = None

    # Currenty hypothesis as automata (None if obs table is not complete)
    _cur_hyp = None

    # Current suspected distinguisher suffix
    _sus_suffix = None

    def __init__(self, alpha):
        """Initialize with an alphabet"""
        self.alpha = alpha
        self.prefixes = set()
        self.distinguishers = []
        # Next queries to complete obs table ?
        self.next_complete = set()

        # Every observation result so far
        self.obs = {}

#        # Are we in the CEX analysis phase (queries to find next
#        # distinguisher) this is the case if _cur_hyp is True and
#        # _last_meq is filled.
#        self._cur_hyp = TrivialA(alpha, False)
        self.add_prefix(self._empty)
        self.add_distinguisher(self._empty)

    def add_prefix(self, p):
        self.prefixes.add(p)
        for x in self.alpha + [self._empty]:
            for dist in self.distinguishers:
                t = p + x + dist
                if t not in self.obs:
                    self.next_complete.add(t)

    def add_distinguisher(self, dist):
        self.distinguishers.append(dist)
        for p in self.prefixes:
            for x in self.alpha + [self._empty]:
                t = p + x + dist
                if t not in self.obs:
                    self.next_complete.add(t)    
    
    def get_membership_query(self):
        """Current required membership query, if any"""
        if self._last_meq is None:
            self._last_meq  = min(self.next_complete)
        return self._last_meq
        
    def get_hypothesis(self):
        """Returns hypothesis or None if membership queries are waiting"""
        if self._sus_suffix is None:
            return self._cur_hyp

    def answer_membership_query(self, answer):
        """Answer current membership query"""
        self.get_membership_query() # enforce _last_meq is filled in
        self.obs[self._last_meq] = answer
        if self._last_meq in self.next_complete:
            self.next_complete.remove(self._last_meq)

        # are we in CEX analysis mode or not ?
#        if self._cur_hyp is None:
#            pass
#        elif self._sus_suffix is not None: # CEX analysis
#            if answer == self._cex_expected:
#                self.add_distinguisher(self._sus_suffix)
#                self._cur_hyp = self._sus_suffix = None
#                assert(self.next_complete) # Progress should be made here
#                print("cex analysis done")
#            else:
#                self._cex_analysis(self._sus_suffix)
#        else:
#            raise NotImplementedError("You should first return a CEX")

        self._last_meq = None
        if len(self.next_complete) == 0:
            self._attempt_build()


    def _vector_of(self, w):
        """For a given prefix w, build the vector of accetance.
        Here: as an int (but any hashable type would do)"""
        i = 1
        v = 0
        for dist in self.distinguishers:
            if self.obs[w + dist]:
                v += i
            i <<= 1
        return v

    def _attempt_build(self):
        """Attemps to build an hypothesis, or add some missing prefixes.
        Internally, the states are the prefixes.
        """
        print("attempt")
        states = {self._vector_of(p):p for p in sorted(self.prefixes)}
        tab = {}
        for p in sorted(self.prefixes):
            tab[p] = []
            for x in self.alpha:
                succ = p + x
                if succ in self.prefixes:
                    tab[p].append(succ)
                else:
                    v = self._vector_of(succ)
                    if v not in states:
                        # We add succ as a prefix (we continue the loop in
                        # case this happens for other words)
                        states[v] = succ
                        self.add_prefix(succ)
                    else:
                        tab[p].append(states[v])
        if not self.next_complete:
            # Recall that the emptyword was the first distinguisher
            acc = {states[v] for v in states if v%2 ==1 }
            self._cur_hyp = DFAFromTab(self.alpha, tab, "", acc)
    
    def feed_cex(self, word):
        """Naive: add all suffixes"""
        for i in range(len(word)):
            self.add_distinguisher(word[i:])
        self._cur_hyp = None

#    def feed_cex_old(self, word):
#        """Feed a counter example to the current hypothesis"""
#        assert(self._cur_hyp is not None)
#        word = "".join(word)
#        self._cex_expected = not self._cur_hyp.is_accepting(word)
#        self._cex_analysis(word)
#
#    def _cex_analysis(self, word):
#        """feed next membership query for cex analysis"""
#        ext = self._empty
#        for (i,l) in enumerate(word):
#            ext += l
#            if ext not in self.prefixes:
#                self._sus_suffix = word[i+1:]
#                prefix = next(self._cur_hyp.getSucc(ext[:-1], ext[-1]))
#                self._last_meq = prefix + self._sus_suffix
#                break

class DFAFromTab(NFA):
    def __init__(self, alphabet, tab, init, acc):
        super().__init__(alphabet)
        self.tab = tab
        self.init = init
        self.acc = acc
        self.ith_letter = {alphabet[i]:i for i in range(len(alphabet))}

    def get_initial(self):
        yield self.init
#    def getNbStates(self):
#        return len(self.tab)
#    
    def get_succ(self, src, letter):
        yield self.tab[src][self.ith_letter[letter]]

    def is_acceptingWord(self, s, word):
        for l in word:
            src = next(self.get_succ(s, l))
        return self.is_accepting(s)
    
    def is_accepting(self, s):
        return s in self.acc

def manual_equivalence_oracle(auto):
    """Show an automaton and asks for a counterexample"""
    auto.show("Here is my hypothesis, provide a counterexample please")
    return input()

if __name__ == '__main__':
    # Learn the target (ab + aab)+
    
    # TODO: we don't learn the * because of a flaw in the protocol design
    # for the java interface :x
    target = automata.Kleene(automata.Disjunction(
        automata.SingleWordAcceptor("ab"),
        automata.SingleWordAcceptor("aab"),
    ), plus=True)
    target = automata.Determinization(target)
    target.show()

    # Learner
    alpha = target.alphabet
    l = JavaLStar(alpha)
    #l = Lstar(alpha)
    #print(automata.find_word(automata.Intersection(target,
    #    automata.SingleWordAcceptor("aab", alpha))))
    while True:
        while l.get_hypothesis() is None:
            w = l.get_membership_query()
            print("Query %r" % w)
            auto = automata.Intersection(target,
                          automata.SingleWordAcceptor(w, alpha))
            #auto.show("Queried automata")
            answer = automata.find_word(auto) is not None
            print(" --> answer: %r" % (answer,))
            l.answer_membership_query(answer)
        l.get_hypothesis().show("Hypothesis")
        pos_cex = automata.find_word(
                automata.Difference(target, l.get_hypothesis()))
        if pos_cex is not None:
            pos_cex = "".join(pos_cex)
            print(" --> Positive Counterexample %r" % pos_cex)
            l.feed_cex(pos_cex)
            continue

        neg_cex = automata.find_word(
                automata.Difference(l.get_hypothesis(), target))
        if neg_cex is not None:
            neg_cex = "".join(neg_cex)
            print(" --> Negative Counterexample %r" % neg_cex)
            l.feed_cex(neg_cex)
            continue
        print("No cex found, terminating")
        break
