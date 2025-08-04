#!/bin/env python3
import os
import operator
import subprocess
import IPython
import itertools, re
#from graphviz import Source
from IPython.display import Image, display


class CachedIterator(object):
    def __init__(self, it):
        self.it = iter(it)
        # current value (next one to be returned by next(),
        # if already queried)
        self.cur = None
        # already queried ?
        self.already = False
        # is the iterator over ?
        self.done = False

    def has_next(self):
        if not self.already:
            self.already = True
            try:
                self.cur = next(self.it)
            except StopIteration:
                self.done = True
        # now, we know:
        return not self.done
    
    def __next__(self):
        if not self.has_next():
            raise StopIteration
        self.already = False
        return self.cur

def cross_it(la, lb):
    na, nb = len(la), len(lb)
    i, j = max(0, na-nb), (nb-1)
    while j>=0 and i < na:
        yield (la[i],lb[j])
        i += 1
        j -= 1

def product_generator(gena, genb):
    # Accumulators of already generated elements of gena and genb (resp.)
    acca, accb = [], []
    gena, genb = CachedIterator(gena), CachedIterator(genb)
    while gena.has_next() and genb.has_next():
        acca.append(next(gena))
        accb.append(next(genb))
        yield from cross_it(acca, accb)
    
    while acca and accb:
        if not gena.has_next() and not genb.has_next():
            acca.pop(0)
            accb.pop(0)
        if gena.has_next():
            acca.append(next(gena))
        if genb.has_next():
            accb.append(next(genb))
        yield from cross_it(acca, accb)

class NFA(object):
    """Abstract class of NFA"""
    def __init__(self, alphabet):
        """Initialize with some alphabet (any iterable would do)"""
        if self.__class__ == NFA:
            raise NotImplementedError("Abstract")
        self.alphabet = alphabet

    def get_states(self):
        """Iterator on all states"""
        todo = list(self.get_initial())
        visited = set(todo)
        for s in todo:
            yield s
            for a in self.alphabet:
                for d in self.get_succ(s, a):
                    if d not in visited:
                        visited.add(d)
                        todo.append(d)

    _state_space = None
    def get_nb_states(self):
        """Returns number of states (feel free to override)"""
        if self._state_space is None:
            todo = list(self.get_initial())
            visited = set(todo)
            for s in todo:
                for a in self.alphabet:
                    for d in self.get_succ(s, a):
                        if d not in visited:
                            visited.add(d)
                            todo.append(d)
            self._state_space = visited
        return len(self._state_space)

    def get_succ(self, src, letter):
        """Returns a generator of successors"""
        raise IndexError("Src out of range")

    def get_initial(self):
        """Returns a generator of the initial states"""
        yield from ()  # empty generator

    def is_accepting(self, st):
        """If this state accepting ?"""
        return False

    def membership(self, word):
        """Check if the word (list of letters) is accepted"""
        cur = set(self.get_initial())
        for x in word:
            for st1 in cur:
                tmp = set()
                n_state = self.get_succ(st1, x)
                for i in n_state:
                    tmp.add(i)
                cur = tmp
        return any(self.is_accepting(st) for st in cur)
        
    def is_deterministic(self):
        """Is deterministic (feel free to override)"""
        if len(list(self.get_initial())) > 1:
            return False
        for st in self.get_states():
            for x in self.alphabet:
                if len(list(self.get_succ(st, x))) > 1:
                    return False
        return True

    def is_complete(self):
        """Is comptelete (feel free to override)"""
        if len(list(self.get_initial())) == 0:
            return False
        for st in range(self.get_nb_states()):
            for x in self.alphabet:
                if len(list(self.get_succ(st, x))) == 0:
                    return False
        return True 
    
    def show(self, title=""):
        dot = subprocess.Popen(['/usr/bin/dot', '-Tpng'],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE)
        
        if IPython.get_ipython().__class__.__name__ == 'ZMQInteractiveShell':
            def final_show():
                nonlocal dot
                return Image(data=dot.communicate()[0])
        else:
            feh = subprocess.Popen(['/usr/bin/feh', '-'], stdin=dot.stdout)
            def final_show():
                nonlocal feh, dot
                dot.stdin.flush()
                dot.stdin.close()
                dot.wait()
                feh.wait()
                
        def formatL(x):
            """Format label"""
            return (str(x).encode())
        states_id = {}
        def formatS(x):
            """Format state, should be a valid identifier for graphviz.
            It should also be unique..."""
            key = str(x)
            ident = re.sub('[^0-9a-zA-Z]+', '_', key)
            if key not in states_id:
                for suff in itertools.chain([''], itertools.count()):
                    if ident + suff not in states_id.values():
                        ident = ident + suff
                        states_id[key] = b"s%s" % (ident.encode())
                        break
            return states_id[key]
            
        dot.stdin.write(b'digraph {\n')
        todo = []
        visited = set()
        for src in self.get_initial():
            todo.append(src)
            visited.add(src)
            dot.stdin.write(b'init_%(s)s [shape = point]; init_%(s)s -> %(s)s;\n' % 
                {b's': formatS(src)})
        for src in todo:
            if self.is_accepting(src):
                dot.stdin.write(b'%s [shape=doublecircle];\n' % formatS(src))
            for x in self.alphabet:
                for dst in self.get_succ(src, x):
                    if dst not in visited:
                        todo.append(dst)
                        visited.add(dst)
                    dot.stdin.write(b'%s -> %s [label="%s"];\n'% \
                        (formatS(src), formatS(dst), formatL(x)))
        if title:
            dot.stdin.write(b'labelloc="t";')
            dot.stdin.write(b'label="%s";' % title.encode())
        dot.stdin.write(b'}\n')
        
        if IPython.get_ipython().__class__.__name__ == 'ZMQInteractiveShell':
            return display(final_show())
        else:
            return final_show()
    
    def show_graphviz(self, title=""):
        """Show in dot format"""
        # dot test.dot -Tpng | feh 
        dot = ""
        def formatL(x):
            return (str(x))
        def formatS(x):
            return f"s{str(x)}"

        dot+= ('digraph {\n')
        todo = []
        visited = set()
        for src in self.get_initial():
            todo.append(src)
            visited.add(src)
            dot+= ('init_%(s)s [shape = point]; init_%(s)s -> %(s)s;\n' % 
                {'s': formatS(src)})
        for src in todo:
            if self.is_accepting(src):
                dot+= ('%s [shape=doublecircle];\n' % formatS(src))
            for x in self.alphabet:
                for dst in self.get_succ(src, x):
                    if dst not in visited:
                        todo.append(dst)
                        visited.add(dst)
                    dot+= ('%s -> %s [label="%s"];\n'% \
                        (formatS(src), formatS(dst), formatL(x)))
        #dot+= ('%d -> %d [label="a"];\n' % (0,1))
        # if title:
            # dot+= ('labelloc="t";')
            # dot+= ('label="%s";' % title.encode())
        dot+= ('}\n')
        if not os.path.exists("graphs"):
            os.makedirs("graphs")
        with open(f"graphs/{title}.gv", 'w') as file:
            file.write(dot) 
        # s = Source(dot, "tests/test", format="png")
        # s.view()
        return dot

    def monaDFA(self, f, variables, varorders):
        """Generate a mona DFA"""
        assert(self.is_deterministic())
        f.write('MONA DFA\n')
        f.write('number of variables: %d\n' % len(variables))
        f.write('variables: %s\n' % ' '.join(variables))
        f.write('orders: %s\n' % ' '.join(map(str, varorders)))
        f.write('states: %d\n' % self.get_nb_states())
        f.write('initial: %d\n' % list(self.get_initial())[0])
        # Let N = number of states, the BDD contains:
        # N leaves and for each state, the decision takes (2^|var| - 1) internal
        # nodes, so in total N+N*(2^|V|-1) = N*2^|V|
        f.write('bdd nodes: %d\n' % ((1<<len(variables))*self.get_nb_states()))

        def acceptGen():
            for st in range(self.get_nb_states()):
                yield "1" if self.is_accepting(st) else "0"
        f.write('final: %s\n' % ' '.join(acceptGen()))
        # offset of the next bdd node encoding a state
        offset = self.get_nb_states()
        # distance between two offsets
        dist = (1<<len(self.variables)) - 1
        behave = list()
        for st in range(offset):
            behave.append(offset+st*dist)
        f.write('behaviour: %s\n' % ' '.join(str(b) for b in behave))
        f.write('bdd:\n')
        # First N bdd nodes are leaves matching each of the N states of the
        # DFA
        for i in range(self.get_nb_states()):
            f.write(' -1 %d 0\n' % i)
        for st in range(self.get_nb_states()):
            for (d,v) in enumerate(variables):
                base = (1<<d)-1
                for node in range(1<<d):
                    parent = base+node
                    left = 2*parent + 1
                    right = left + 1
                    # Need to offset everything
                    parent += offset
                    # Actually, if last variable, need to replace by the leaf
                    if d == len(variables) - 1:
                        left = list(self.get_succ(st, left))[0]
                        right = list(self.get_succ(st, right))[0]
                    else:
                        left += offset
                        right += offset
                    f.write(' %d %d %d\n' % (d, left, right))
            offset += dist
        f.write('end\n')

    def to_regex(self, builder):
        """Return an equivalent regex, using Brzozowski/McCluskey"""
        # Post: dictionnary, for every state, of successors.
        # one successor = dict (k,v) where k=destination state, v=output (label)
        post = {}
        # Pre: same but backward transitions
        pre = {}
        # extra state for beginning and finish (not the same)
        bot = None
        epsilon = builder.get_epsilon()
        empty = builder.get_empty()
        def plus(a,b):
            if a == empty:
                return b
            if b == empty:
                return a
            return builder.plus(a, b)

        def concat(a, b):
            if empty in [a,b]:
                return empty
            if a == epsilon:
                return b
            if b == epsilon:
                return a
            return builder.concat(a, b)
        
        def star(a):
            if a == empty:
                return epsilon
            return builder.star(a)

        # Fill post and pre
        pre[bot] = {bot: empty}
        post[bot] = {bot: empty}
        for s in self.get_states():
            post.setdefault(s, {})
            pre.setdefault(s, {})
            if self.is_accepting(s):
                post[s][bot] = epsilon
                pre[bot][s] = epsilon
            for x in self.alphabet:
                l = builder.from_letter(x)
                for d in self.get_succ(s, x):
                    #print(f"{s} --(x)--> {d}")
                    pre.setdefault(d, {})
                    pre.setdefault(s, {})

                    post[s][d] = plus(post[s].get(d, empty), l)
                    pre[d][s] = plus(pre[d].get(s, empty), l)

        for s in self.get_initial():
            pre[s][bot] = epsilon
            post[bot][s] = epsilon
        # proceed to eliminate states
        for q in self.get_states():
            if q in post[q]:
                loop = star(post[q][q])
#                print(f"star on {post[q][q]}")
            else:
                loop = epsilon
            for s in pre[q]:
                for d in post[q]:
                    if d == q:
                        continue
                    # We're doing the path from s through q (with loops) to d
                    l = concat(pre[q][s], concat(loop, post[q][d]))
                    # add previous label from s to d as an alternative
                    if d in post[s]:
                        l = plus(post[s][d], l)
                    post[s][d] = pre[d][s] = l
                    # delete q
                    post[s][q] = empty
                    pre[d][q] = empty
            post[q] = pre[q] = {}
#            print(f"After deleting {q}")
#            print(post)
        return post[bot][bot]

    def to_ostrich_auto(self):
        """Convert to ostrich automaton"""
        out = "automaton value_0 {\n"
        def fstate(st):
            """How to format a state"""
            return f"q{str(st)}"
        out += "  init " + ",".join(map(fstate, self.get_initial())) + ";\n"
        todo = list(self.get_initial())
        acc = list()
        visited = set(todo)
        while todo:
            s = todo.pop()
            if self.is_accepting(s):
                acc.append(s)
            for a in self.alphabet:
                for d in self.get_succ(s, a):
                    if d not in visited:
                        visited.add(d)
                        todo.append(d)
                    out += f"  {fstate(s)} -> {fstate(d)} [{ord(a)},{ord(a)}];\n"
        # Ostrich wants a non-empty list here
        if acc:
            out += f"  accepting {','.join(map(fstate, acc))};\n"
        else:  # TODO fresh state symbol
            out += "   accepting nostate;\n"
        out += "}\n"

        return out
    
    def to_ostrich_interleaving_transducer_without_pad(self, name="auto", preamble=False, pad = 'p'):
        """convert into smt2lib format to be eaten by an ostrich"""
        
        res = ""
        def print(s):
            nonlocal res
            res += s + "\n"
        if preamble:
            print("(set-logic QF_S)\n(set-option :parse-transducers true)")
        x = "x"
        y = "y"
        e = "-"
        tab = "  "
        init = list(self.get_initial())
        if len(init) != 1:
            raise NotImplementedError("More or less than one initial "+ \
                "state(s)is not supported, sorry.")

        def l(state):
            """label of a state"""
            if state in init:
                return name
            else:
                return f"{name}_{str(state)}"

        print(f"(define-funs-rec (")
        tmp_num = 0
        for q in self.get_states():
            print(f"{tab*2} ({l(q)} " + \
                    f"(({x} String) ({y} String)) Bool)")
            tmp_num += 1
        print(f"{tab*2} ({l(tmp_num)} " + \
                    f"(({x} String) ({y} String)) Bool)")
        print(f"{tab})(")
        for q in self.get_states():
            print(f"{tab*2}; {l(q)}")
            print(f"{tab*2}(or")
            print(f'{tab*4}(and (= {x} "") (= {y} ""))')
            for a in self.alphabet:
                if a == "a":
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} "")) (not (= {y} "")) (not (= (str.head {x}) (char.from-int (str.to_code "{pad}"))))')
                        print(f'{tab*4}     (= (str.head_code x) (str.head_code y))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) (str.tail {y}))')
                        print(f'{tab*4})')
                        print(f'{tab*4}(and (not (= {x} "")) (= (str.head {x}) (char.from-int (str.to_code "{pad}")))')
                        print(f'{tab*4}  ({l(tmp_num)} (str.tail {x}) {y})')
                        print(f'{tab*4})')
                else:
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} ""))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) {y})')
                        print(f'{tab*4})')
            print(f"{tab*2})")
        print(f"{tab*2}; {l(tmp_num)}")
        print(f"{tab*2}(or")
        print(f'{tab*4}(and (= {x} "") (= {y} ""))')

        print(f'{tab*4}(and (not (= {x} ""))')
        print(f'{tab*4}  ({l(tmp_num)} (str.tail {x}) {y})')
        print(f'{tab*4})')
        print(f"{tab*2})")


        print(f"{tab})\n)")
        return res

    def to_ostrich_interleaving_transducers(self, name="auto", preamble=False , pad = 'p'):
        """convert into smt2lib format to be eaten by an ostrich"""
        
        res = ""
        def print(s):
            nonlocal res
            res += s + "\n"
        if preamble:
            print("(set-logic QF_S)\n(set-option :parse-transducers true)")
        x = "x"
        y = "y"
        e = "-"
        tab = "  "
        init = list(self.get_initial())
        if len(init) != 1:
            raise NotImplementedError("More or less than one initial "+ \
                "state(s)is not supported, sorry.")

        def l(state):
            """label of a state"""
            if state in init:
                return name
            else:
                return f"{name}_{str(state)}"

        print(f"(define-funs-rec (")
        for q in self.get_states():
            print(f"{tab*2} ({l(q)} " + \
                    f"(({x} String) ({y} String)) Bool)")
        print(f"{tab})(")
        for q in self.get_states():
            print(f"{tab*2}; {l(q)}")
            print(f"{tab*2}(or")
            print(f'{tab*4}(and (= {x} "") (= {y} ""))')
            for a in self.alphabet:
                if a == "a":
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} "")) (= (str.head {x}) (char.from-int (str.to_code "{pad}")))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) {y})')
                        print(f'{tab*4})')
                        print(f'{tab*4}(and (not (= {x} "")) (not (= {y} "")) (not (= (str.head x) (char.from-int (str.to_code "{pad}"))))')
                        print(f'{tab*4}     (= (str.head_code x) (str.head_code y))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) (str.tail {y}))')
                        print(f'{tab*4})')
                else:
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} ""))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) {y})')
                        print(f'{tab*4})')
            print(f"{tab*2})")
        print(f"{tab})\n)")
        return res



    def to_ostrich_interleaving_transducer_pad(self, name="auto", preamble=False):
        """convert into smt2lib format to be eaten by an ostrich"""
        
        res = ""
        def print(s):
            nonlocal res
            res += s + "\n"
        if preamble:
            print("(set-logic QF_S)\n(set-option :parse-transducers true)")
        x = "x"
        y = "y"
        e = "-"
        tab = "  "
        init = list(self.get_initial())
        if len(init) != 1:
            raise NotImplementedError("More or less than one initial "+ \
                "state(s)is not supported, sorry.")

        def l(state):
            """label of a state"""
            if state in init:
                return name
            else:
                return f"{name}_{str(state)}"

        print(f"(define-funs-rec (")
        for q in self.get_states():
            print(f"{tab*2} ({l(q)} " + \
                    f"(({x} String) ({y} String)) Bool)")
        print(f"{tab})(")
        for q in self.get_states():
            print(f"{tab*2}; {l(q)}")
            print(f"{tab*2}(or")
            print(f'{tab*4}(and (= {x} "") (= {y} ""))')
            for a in self.alphabet:
                if a == "a":
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} "")) (= (str.head {x}) (char.from-int (str.to_code "{pad}")))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) {y})')
                        print(f'{tab*4})')
                        print(f'{tab*4}(and (not (= {x} "")) (not (= {y} "")) (not (= (str.head x) (char.from-int (str.to_code "{pad}"))))')
                        print(f'{tab*4}     (= (str.head_code x) (str.head_code y))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) (str.tail {y}))')
                        print(f'{tab*4})')
                else:
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} ""))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) {y})')
                        print(f'{tab*4})')
            print(f"{tab*2})")
        print(f"{tab})\n)")
        return res

    def to_pcp_ostrich_concat_transducer(self, name="auto", preamble=False):
        """convert into smt2lib format to be eaten by an ostrich"""
        
        res = ""
        def print(s):
            nonlocal res
            res += s + "\n"
        if preamble:
            print("(set-logic QF_S)\n(set-option :parse-transducers true)")
        x = "x"
        y = "y"
        e = "-"
        tab = "  "
        init = list(self.get_initial())
        if len(init) != 1:
            raise NotImplementedError("More or less than one initial "+ \
                "state(s)is not supported, sorry.")

        def l(state):
            """label of a state"""
            if state in init:
                return name
            else:
                return f"{name}_{str(state)}"

        print(f"(define-funs-rec (")
        for q in self.get_states():
            print(f"{tab*2} ({l(q)} " + \
                    f"(({x} String) ({y} String)) Bool)")
        print(f"{tab})(")
        for q in self.get_states():
            print(f"{tab*2}; {l(q)}")
            print(f"{tab*2}(or")
            print(f'{tab*4}(and (= {x} "") (= {y} ""))')
            for a in self.alphabet:
                if a == "a":
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} "")) (not (= {y} ""))')
                        print(f'{tab*4}     (= (str.head_code x) (str.head_code y))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) (str.tail {y}))')
                        print(f'{tab*4})')
                else:
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} ""))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) {y})')
                        print(f'{tab*4})')
            print(f"{tab*2})")
        print(f"{tab})\n)")
        return res

    # def to_ostrich_interleaving_transducer(self, name="auto", preamble=False, pad = "#"):
    #     """convert into smt2lib format to be eaten by an ostrich"""
        
    #     res = ""
    #     def print(s):
    #         nonlocal res
    #         res += s + "\n"
    #     if preamble:
    #         print("(set-logic QF_S)\n(set-option :parse-transducers true)")
    #     x = "x"
    #     y = "y"
    #     e = "-"
    #     tab = "  "
    #     init = list(self.get_initial())
    #     if len(init) != 1:
    #         raise NotImplementedError("More or less than one initial "+ \
    #             "state(s)is not supported, sorry.")

    #     def l(state):
    #         """label of a state"""
    #         if state in init:
    #             return name
    #         else:
    #             return f"{name}_{str(state)}"

    #     print(f"(define-funs-rec (")
    #     for q in self.get_states():
    #         print(f"{tab*2} ({l(q)} " + \
    #                 f"(({x} String) ({y} String)) Bool)")
    #     print(f"{tab})(")
    #     for q in self.get_states():
    #         print(f"{tab*2}; {l(q)}")
    #         print(f"{tab*2}(or")
    #         print(f'{tab*4}(and (= {x} "") (= {y} ""))')
    #         for a in self.alphabet:
    #             if a == "a":
    #                 for d in self.get_succ(q, a):
    #                     print(f'{tab*4}(and (not (= {x} "")) (not (= {y} ""))')
    #                     print(f'{tab*4}     (= (str.head_code x) (str.head_code y))')
    #                     print(f'{tab*4}  ({l(d)} (str.tail {x}) (str.tail {y}))')
    #                     print(f'{tab*4})')
    #             else:
    #                 for d in self.get_succ(q, a):
    #                     print(f'{tab*4}(and (not (= {x} ""))')
    #                     print(f'{tab*4}  ({l(d)} (str.tail {x}) {y})')
    #                     print(f'{tab*4})')
    #         print(f"{tab*2})")
    #     print(f"{tab})\n)")
    #     return res
    
    def to_ostrich_concat_transducer(self, name="auto", preamble=False, pad = '#'):
        """convert into smt2lib format to be eaten by an ostrich"""
        res = ""
        def print(s):
            nonlocal res
            res += s + "\n"
        if preamble:
            print("(set-logic QF_S)\n(set-option :parse-transducers true)")
        x = "x"
        y = "y"
        e = "-"
        tab = "  "
        init = list(self.get_initial())
        if len(init) != 1:
            raise NotImplementedError("More or less than one initial "+ \
                "state(s)is not supported, sorry.")

        def l(state):
            """label of a state"""
            if state in init:
                return name
            else:
                return f"{name}_{str(state)}"

        print(f"(define-funs-rec (")
        for q in self.get_states():
            print(f"{tab*2} ({l(q)} " + \
                    f"(({x} String) ({y} String)) Bool)")
        print(f"{tab})(")
        for q in self.get_states():
            print(f"{tab*2}; {l(q)}")
            print(f"{tab*2}(or")
            print(f'{tab*4}(and (= {x} "") (= {y} ""))')
            for a in self.alphabet:
                if a == "a":
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} "")) (not (= {y} ""))')
                        print(f'{tab*4}     (= (str.head_code x) (str.head_code y))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) (str.tail {y}))')
                        print(f'{tab*4})')
                else:
                    for d in self.get_succ(q, a):
                        print(f'{tab*4}(and (not (= {x} ""))')
                        print(f'{tab*4}  ({l(d)} (str.tail {x}) {y})')
                        print(f'{tab*4})')
            print(f"{tab*2})")
        print(f"{tab})\n)")
        return res

def to_ostrich_concat_transducer(len, ith, name="auto", preamble=False, pad = '#'):
    res = ""
    tab = "  "
    def print(s):
        nonlocal res
        res += s + "\n"
    if preamble:
        print("(set-logic QF_S)\n(set-option :parse-transducers true)")
    print(f"(define-funs-rec (({name} ((x String) (y String)) Bool)")
    for i in range(len-1):
        print(f"{tab*2} ({name}{i+1} ((x String) (y String)) Bool)")
    if ith != len - 1:
        print(f"{tab*2} ({name}{len} ((x String) (y String)) Bool)")
    print(f"{tab})(")
    if ith == len - 1:
        for i in range(len - 1):
            if i == 0:
                print(f"""(or (and (= x "") (= y ""))
            (and (not (= x ""))
                (not (= (str.head x) (char.from-int (str.to_code "{pad}"))))  
                ({name} (str.tail x) y))
            (and (not (= x ""))
                (= (str.head x) (char.from-int (str.to_code "{pad}")))        
                ({name}{i+1} (str.tail x) y)))""")
            else:
                print(f"""(or (and (= x "") (= y ""))
            (and (not (= x ""))
                (not (= (str.head x) (char.from-int (str.to_code "{pad}"))))  
                ({name}{i} (str.tail x) y))
            (and (not (= x ""))
                (= (str.head x) (char.from-int (str.to_code "{pad}")))        
                ({name}{i+1} (str.tail x) y)))""")
        print(f"""(or (and (= x "") (= y ""))
        (and (not (= x "")) (not (= y ""))
             (= (str.head x) (str.head y))
             ({name}{len-1} (str.tail x) (str.tail y)))
        )))""")
    else:

        for i in range(len):
            if i == 0 and ith == 0:
                print(f"""(or (and (= x "") (= y ""))
            (and (not (= x "")) (not (= y ""))
                (= (str.head x) (str.head y))
                (not (= (str.head x) (char.from-int (str.to_code "{pad}"))))  
                ({name} (str.tail x) (str.tail y)))
            (and (not (= x ""))
                (= (str.head x) (char.from-int (str.to_code "{pad}")))        
                ({name}{i+1} (str.tail x) y)))""")
            elif i == 0: 
                print(f"""(or (and (= x "") (= y ""))
            (and (not (= x ""))
                (not (= (str.head x) (char.from-int (str.to_code "{pad}"))))  
                ({name} (str.tail x) y))
            (and (not (= x ""))
                (= (str.head x) (char.from-int (str.to_code "{pad}")))        
                ({name}{i+1} (str.tail x) y)))""")
            elif i == ith:
                print(f"""(or (and (= x "") (= y ""))
            (and (not (= x "")) (not (= y ""))
                (= (str.head x) (str.head y))
                (not (= (str.head x) (char.from-int (str.to_code "{pad}"))))  
                ({name}{i} (str.tail x) (str.tail y)))
            (and (not (= x ""))
                (= (str.head x) (char.from-int (str.to_code "{pad}")))        
                ({name}{i+1} (str.tail x) y)))""")
            else:
                print(f"""(or (and (= x "") (= y ""))
            (and (not (= x ""))
                (not (= (str.head x) (char.from-int (str.to_code "{pad}"))))  
                ({name}{i} (str.tail x) y))
            (and (not (= x ""))
                (= (str.head x) (char.from-int (str.to_code "{pad}")))        
                ({name}{i+1} (str.tail x) y)))""")
        print(f"""    (or (and (= x "") (= y ""))
            (and (not (= x ""))
                ({name}{len} (str.tail x) y)))
    ))""")
    return res
    

    


class MatrixNFA(NFA):
    """A NFA defined by a matrix.
    Ie a list of dictionnaries. Each entry of every dict is index by a letter
    and has value a list of successors"""
    def __init__(self, init, acc, mat, alpha=None):
        if hasattr(mat, 'values'):
            values = mat.values()
        else:
            values = mat
        used_letters = set(a for tr in mat for a in tr)
        if alpha is None:
            alpha = list(used_letters)
        elif not used_letters.issubset(alpha):
            raise ValueError("MatrixNFA: given matrix contains more used "+\
                "letters than provided alphabet")
        super().__init__(alpha)
        self.init = init
        self.acc = acc
        self.mat = mat

    def get_initial(self):
        yield from self.init

    def is_accepting(self, src):
        return src in self.acc

    def get_succ(self, src, letter):
        yield from self.mat[src].get(letter, [])

class TrivialA(NFA):
    """Most trivial automaton. Accepting -* where - is the only letter"""
    def __init__(self, alpha, acc=True):
        super().__init__(alpha)
        self.acc = acc

    def get_nb_states(self):
        return 1

    def get_succ(self, src, letter):
        assert(src == 0 and letter == self.alphabet[0])
        yield 0

    def get_initial(self):
        yield 0

    def is_accepting(self, st):
        assert(st == 0)
        return self.acc


NFA.trivial = TrivialA([None])

class ModulusUnary(NFA):
    def __init__(self, n, p):
        """the automaton for all words encoding n modulo p"""
        super().__init__(range(1))
        self.n = n
        self.p = p

    def get_nb_states(self):
        return self.p

    def get_succ(self, src, letter):
        yield (src + 1) % self.p

    def get_initial(self):
        yield 0

    def is_accepting(self, st):
        return st == self.n

class ModulusBinary(NFA):
    def __init__(self, n, p):
        super().__init__(range(2))
        self.n = n
        self.p = p

    def get_nb_states(self):
        return self.p

    def get_succ(self, src, letter):
        assert(letter in self.alphabet)
        yield (2*src + letter) % self.p

    def get_initial(self):
        yield 0

    def is_accepting(self, st):
        return st == self.n

class Determinization(NFA):
    """Determinization (and completion) of a NFA, given as an input, lazy
    construction"""
    # Internally, we built the powerset automaton.
    # internal states are sorted tuples of states (int) from the input NFA

    def __init__(self, ref):
        """ref is an automaton to determinize"""
        super().__init__(ref.alphabet)
        self.ref = ref

        # As the power construction uses sets of states of the original
        # automaton, we need a mapping between these sets and their number
        # Instead of sets, we use ordered tuples
        self._tuple2int = dict() # from a set of states to its int new state
        self._int2tuple = list()

        self._succ = list() # list of successors, if already computed (not in
                            # open set anymore

        initial_t = tuple(sorted(self.ref.get_initial()))
        src = self._get_state(initial_t)
        assert src == 0

    def _get_state(self, t):
        """Returns the state (int) from a given tuple,
        initializes the succ if necessary."""
        if t not in self._tuple2int:
            st = len(self._int2tuple)

            self._int2tuple.append(t)
            self._succ.append({})
            self._tuple2int[t] = st
            return st
        else:
            return self._tuple2int[t]
    
    def get_initial(self):
        yield 0

    def get_succ(self, src, l):
        if len(self._succ) < src:
            raise IndexError("Src out of range")
        
        if l not in self._succ[src]:
            src_t = self._int2tuple[src]
            dst_set = set(d for s in src_t for d in self.ref.get_succ(s, l) )
            self._succ[src][l] = self._get_state(tuple(sorted(dst_set)))
        yield self._succ[src][l]

    def is_accepting(self, st):
        """If this state accepting ?"""
        return any(self.ref.is_accepting(s) for s in self._int2tuple[st])


class Minimization(NFA):
    def __init__(self, auto):
        super().__init__(auto.alphabet)
        assert(auto.is_deterministic())
        self.auto = auto
        self._rep = self._representatives(auto)

    def get_initial(self):
        for st in self.auto.get_initial():
            yield self._rep[st]
            break
    
    def is_accepting(self, st):
        return self.auto.is_accepting(st)

    def get_succ(self, src, letter):
        for dst in self.auto.get_succ(self._rep[src], letter):
            yield self._rep[dst]

    def _representatives(self, auto):
        """Compute the table of representatives, one for each state"""
        alpha = list(auto.alphabet)
        def succ(st):
            """Generator of all successors, for any letter"""
            for a in alpha:
                yield from auto.get_succ(st, a)
        
        # Final answer to return: state -> representative (another state)
        rep = {}
        # Acceptance status -> representative (= a state)
        by_acc = {}
        # for a given state, list of predecessors
        pred = {}
        for st in auto.get_states():
            acc = auto.is_accepting(st)
            if acc not in by_acc:
                by_acc[acc] = st
            rep[st] = by_acc[acc]
            # fill in the list of predecessors
            for dst in succ(st):
                pred.setdefault(dst, [])
                pred[dst].append(st)
        
        # todo list of classes to refine
        todo = set(by_acc.values())
        while todo:
            # representative of a class to analyse
            st_repr = todo.pop()
            # The images: tuple of successors -> list of states
            images = {}
            if (st_repr not in rep.values()):
                print(st_repr)
            assert(st_repr in rep.values())
            for st in rep.keys():
                if rep[st] != st_repr:
                    continue
                t = tuple(succ(st))
                images.setdefault(t, [])
                images[t].append(st)
            
            
            assert(len(images) > 0)
            if len(images)==1: # all states in the class have the same succ's
                continue
            # otherwise, more than two different tuples
            for cl in images.values():
                # set a new representative (first one in the class)
                for nst in cl:
                    rep[nst] = cl[0]
                    # register predecessors to explore
                    for src in pred[nst]:
                        todo.add(src)

            # Compress todo to set of representatives
            todo = set(rep[st] for st in todo)
        return rep

class Negation(Determinization):
    """Negation of a NFA, given as an input, lazy
    construction with built-in determinization"""
    def __init__(self, ref):
        super().__init__(ref)

    def is_accepting(self, s):
        return not super().is_accepting(s)

class Product(NFA):
    """Automaton on the product of two automaton. The alphabet is the product
    alphabet. On the fly construction."""
    def __init__(self, refa, refb, comb=operator.and_):
        super().__init__(\
            list(product_generator(refa.alphabet, refb.alphabet)))
        self.comb = comb
        self.refa = refa
        self.refb = refb
        self._t2s = {}
        self._s2t = []
    
    def _get_st(self, a, b):
        if (a,b) not in self._t2s:
            self._t2s[(a,b)] = len(self._s2t)
            self._s2t.append((a,b))
        return self._t2s[(a,b)]

    def get_initial(self):
        for sa in self.refa.get_initial():
            for sb in self.refb.get_initial():
                yield self._get_st(sa, sb)

    def get_succ(self, src, letter):
        (sa,sb) = self._s2t[src]
        assert(type(letter) == tuple)
        for ta in self.refa.get_succ(sa, letter[0]):
            for tb in self.refb.get_succ(sb, letter[1]):
                yield self._get_st(ta, tb)
    
    def is_accepting(self, s):
        (sa, sb) = self._s2t[s]
        return self.comb(self.refa.is_accepting(sa),
                         self.refb.is_accepting(sb))

        

class SingleWordAcceptor(NFA):
    def __init__(self, word, alpha=None):
        self.word = word
        self.n = len(word)
        if alpha is None:
            alpha = list(set(word))
        super().__init__(alpha)

    def get_initial(self):
        yield 0

    def is_accepting(self, st):
        return st == self.n

    def get_succ(self, src, letter):
        yield from ()
        if src < self.n and letter == self.word[src]:
            yield (src+1)
            

class Kleene(NFA):
    """Kleene star"""
    def __init__(self, ref, plus=False):
        super().__init__(ref.alphabet)
        self.ref = ref
        self.plus = plus

    def get_initial(self):
        yield from self.ref.get_initial()

    def is_accepting(self, s):
        if not self.plus:
            for src in self.ref.get_initial():
                if src == s:
                    return True
        return self.ref.is_accepting(s)

    def get_succ(self, src, letter):
        output = set()
        for dst in self.ref.get_succ(src, letter):
            yield dst
            output.add(dst)
        if any(self.ref.is_accepting(dst) for dst in output):
            for init in self.ref.get_initial():
                if init not in output:
                    yield init

class Morphism(NFA):
    """Morphism"""
    def __init__(self, ref, alpha, f):
        """f: function from letter in alpha to an iterator of letters
        in the original alphabet (of ref)"""
        super().__init__(alpha)
        self.ref = ref
        self.f = f

    def get_succ(self, src, letter):
        for l in self.f(letter):
            yield from self.ref.get_succ(src, l)

    def get_initial(self):
        yield from self.ref.get_initial()

    def is_accepting(self, st):
        return self.ref.is_accepting(st)

class Intersection(Morphism):
    def __init__(self, a, b):
        assert(set(a.alphabet) == set(b.alphabet))
        def f(l):
            yield (l,l)
        super().__init__(Product(a, b), a.alphabet, f)

class Disjunction(Morphism):
    def __init__(self, a, b):
        assert(set(a.alphabet) == set(b.alphabet))
        def f(l):
            yield (l,l)
        super().__init__(Product(
            Determinization(a), Determinization(b),
            comb=operator.or_), a.alphabet, f)

class Difference(Intersection):
    def __init__(self, a, b):
        super().__init__(a, Negation(b))

class InductiveFalsifier(Morphism):
    def __init__(self, trans, inv):
        self.inv = inv
        self.trans = trans
        super().__init__(Product(Product(inv,trans),
                                 Determinization(inv),
                                 comb=lambda a,b: a and not b),
                         trans.alphabet,
                         self.f)
    def f(self, letter):
        a,b = letter
        yield ((a,(a,b)),b)
                                         
                                 

class Post(Morphism):
    def __init__(self, trans, reg_input, backward=False):
        self._reg_input = reg_input
        f = self._backward_f if backward else self._forward_f
        super().__init__(Product(reg_input, trans), reg_input.alphabet, f)

    def _forward_f(self, letter):
        for a in self._reg_input.alphabet:
            yield (a, (a, letter))

    def _backward_f(self, letter):
        for a in self._reg_input.alphabet:
            yield (a, (letter, a))

def _flatten(t):
    if len(t) < 2:
        return t
    else:
        (a,b) = t
        return _flatten(a) + (b,)

def enumerate_words(auto, l):
    """Returns the list of accepted words of length l"""
    words_to = {i:[()] for i in auto.get_initial()}
    for i in range(l):
        r = {}
        for letter in auto.alphabet:
            for (src, words) in words_to.items():
                for dst in auto.get_succ(src, letter):
                    r[dst] = r.get(dst, []) + [(w,letter) for w in words]
        words_to = r
    
    yield from ()
    for (s,wl) in words_to.items():
        if auto.is_accepting(s):
            for w in wl:
                yield _flatten(w)

def find_word(auto):
    """Returns a shortest accepting word, or None"""
    todo = list(auto.get_initial())
    visited = set(todo)
    pred = {}
    for s in todo:
        if auto.is_accepting(s):
            w = []
            while s in pred:
                (s,l) = pred[s]
                w.append(l)
            return tuple(reversed(w))
        for l in auto.alphabet:
            for dst in auto.get_succ(s, l):
                if dst not in visited:
                    visited.add(dst)
                    pred[dst] = (s,l)
                    todo.append(dst)
    return None

def test_ost():
    auto = MatrixNFA([0], [3], [
        {'A': [1]}, #0
        {'B': [0], 'A': [2]}, #1
        {'B': [1], 'A':[3]}, #2
        {'B': [2]}, #3
    ])
    auto.show()
    print(auto.to_ostrich_auto())

def test_matrix():
    n = 4
    alpha = ['a', 'b']
    auto = MatrixNFA([0], [n],
        [ {a: [i+1] for a in alpha} for i in range(n)] + [{}])
    return auto

def create_interleaving_automata(n, final_state=0):
    """Create a simple automaton with n states, accepting all words
    of length n"""
    alpha = ['a', 'b']
    init = [0]
    acc = [final_state]
    mat = []
    for i in range(n):
        if i < n-1:
            if i + 1 == final_state:
                mat.append({'a': [i+1]})
            else:
                mat.append({'b': [i+1]})
        else:
            mat.append(mat[0])

    return MatrixNFA(init, acc, mat, alpha)

def create_concate_automata(n):
    """Create a simple automaton with n states, accepting all words
    of length n"""
    alpha = ['a', 'b', '#']
    init = [0]
    mat = []
    if n == 0:
        acc = [1]
        mat.append({'a': [1]})  # 0
        mat.append({'b': [1]})  # 1
    else:
        acc = [1]
        mat.append({'b': [1]})
        mat.append({'a': [1]})
    return MatrixNFA(init, acc, mat, alpha)

def create_concate_automata_universal(n):
    alpha = ['a', 'b', '#']
    init = [0]
    mat = []
    if n == 0:
        acc = [1]
        mat.append({'a': [1]})  # 0
        mat.append({'#': [2], 'a' : {1}})  # 1
        mat.append({'b': [3]})
        mat.append({'b': [3]})
    else:
        acc = [1]
        mat.append({'b': [1]})
        mat.append({'a': [1]})
    return MatrixNFA(init, acc, mat, alpha)


if __name__ == '__main__':
    # print(to_ostrich_concat_transducer(2, 0, pad="="))
    auto = create_interleaving_automata(4,1)
    print(auto.to_ostrich_interleaving_transducer_without_pad("extractX"))
    auto.show_graphviz("interleaving")

    

    # auto = create_concate_automata(0)
    # print(auto.to_ostrich_concat_transducer())
    # auto.show_graphviz("123")
    # auto1 = create_interleaving_automata(3,2)
    
