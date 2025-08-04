Skip to content
GitLab
Explore
Sign in
Primary navigation
Project
S
string-chc-lib

Manage

Plan

Code

Build

Deploy

Operate

Monitor

Analyze
pub
string-chc-lib
string-chc-lib
src
ismt.py
ismt.py
user avatar
save the copy files temporarily
Hongjian Jiang authored 1 month ago
5e4a3933
ismt.py
10.32 KiB
#!/bin/env python3
"""Interactive smt2 solver wrapper"""
from enum import Enum
import z3
import json
import os
import select
import subprocess
import sexpdata
import sys
from contextlib import contextmanager
import datetime
import automata
import regex
import config
class ExternalSolverException(Exception):
    def __init__(self, message):
        super().__init__(message)
class Z3BasedSolver():
    
    def __init__(self, path, debug=False, silent=True, native_auto=False):
        if silent:
            stderr = subprocess.DEVNULL
        else:
            stderr = sys.stderr
        try:
            self._proc = subprocess.Popen(path, stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=stderr)
        except FileNotFoundError:
            raise Exception(f"Solver path {path} incorrect (not found), " +\
                "please verify your setup and especially your config.json")
        self.debug = debug
        self.native_auto = native_auto
        self._declared_vars = [set()]
    def _cmd(self, cmd):
        if self.debug:
            print(f"Sending({id(self)}) {cmd}")
        self._proc.stdin.write(cmd.encode('ascii') + b'\n')
        self._proc.stdin.flush()
    def push(self):
        self._cmd('(push 1)')
        self._declared_vars.append(set(self._declared_vars[-1]))
    def pop(self):
        self._cmd('(pop 1)')
        self._declared_vars.pop()
    
    def declare_var(self, v):
        if v not in self._declared_vars[-1]:
            self._declared_vars[-1].add(v)
            self._cmd(v.decl().sexpr())
    def check(self):
        self._cmd('(check-sat)')
        res = self._proc.stdout.readline().decode('ascii').strip()
        match res:
            case 'sat': return z3.sat
            case 'unsat': return z3.unsat
            case 'unknown': return z3.unknown
            case _: raise ExternalSolverException(f"External solver returned with Exception: {res}")
    def add(self, form):
        for v in z3.z3util.get_vars(form):
            self.declare_var(v)
        self._cmd(f"(assert {form.sexpr()})")
    def add_word_membership(self, v, auto, negate=False, flag=None, symbol = False, linear= True):
        """Add a constraint of the form "v in Language(auto)".
        negate= True means "notin" instead of "in"
        flag is a boolean expression enabling this membership.
        """
        # Negate automaton ?
        auto_neg = True
        if auto_neg and negate:
            negate = False
            if symbol:
                auto = auto.complement()
            else:
                auto = automata.Negation(auto)
        if not self.native_auto:
            f = z3.InRe(v, auto.to_regex(regex.Z3Builder()))
            self.add(f)
        else:
            self.declare_var(v)
            if symbol:
                e = auto.to_smt(v)
                if negate:
                    auto = auto.complement()
                    e = auto.to_smt(v)
                self._cmd(e)
            else:
                e = f"(str.in.re {v.sexpr()} " + \
                    f"(re.from_automaton \"{auto.to_ostrich_auto()}\"))"
                if negate:
                    e = f"(not {e})"
                if flag is not None:
                    for v in z3.z3util.get_vars(flag):
                        self.declare_var(v)
                    e = f"(=> {flag.sexpr()} {e})"
                self._cmd(f"(assert {e})")
    def add_interleaving_transducer(self, varin_flag, vars, pad = 'p'):
        if vars is None:
            return
        auto_size = len(vars) + 1
        for i in range(len(vars)):
            auto = automata.create_interleaving_automata(auto_size, i+1)
            if varin_flag:
                transducer_formula = auto.to_ostrich_interleaving_transducer_without_pad(f"extractVarin{i}", preamble= (i == 0), pad = pad)
                # transducer_formula = auto.to_ostrich_interleaving_transducer_without_pad(f"extractVarin{i}", preamble= (i == 0))
            else:
                transducer_formula = auto.to_ostrich_interleaving_transducer_without_pad(f"extractVarout{i}", preamble= (i == 0), pad = pad)
            self._cmd(transducer_formula)
    def add_concat_transducer(self, varin_flag, vars, pad = "#", universal = False):
        if vars is None:
            return
        for i in range(len(vars)):
            auto = automata.create_concate_automata(i)
            if varin_flag:
                if universal:
                    transducer_formula = automata.to_ostrich_concat_transducer(len(vars), i, f"extractVarin{i}", preamble= (i == 0), pad = pad)
                else:
                    transducer_formula = auto.to_ostrich_concat_transducer(f"extractVarin{i}", preamble= (i == 0))
            else:
                if universal:
                    transducer_formula = automata.to_ostrich_concat_transducer(len(vars), i, f"extractVarout{i}", preamble= (i == 0), pad = pad)
                else:
                    transducer_formula = auto.to_ostrich_concat_transducer(f"extractVarout{i}", preamble= (i == 0))
            self._cmd(transducer_formula)
       
        # for i in range(len(vars)):
        #     auto = automata.create_concate_automata(i)
        #     if varin_flag:
        #         transducer_formula = auto.to_ostrich_concat_transducer(f"extractVarin{i}", i)
        #     else:
        #         transducer_formula = auto.to_ostrich_concat_transducer(f"extractVarout{i}", i)
        #     self._cmd(transducer_formula)
                
    def add_new_word_membership(self, v1, v2, trans, flag=None):
        """Add a constraint of the form "v in Language(auto)".
        negate= True means "notin" instead of "in"
        flag is a boolean expression enabling this membership.
        """
       
        e = trans.to_ostrich_transducer()
        self._cmd(f"{e}")
        self._cmd(v1.decl().sexpr())
        self._cmd(v2.decl().sexpr())
        self._cmd(f"(assert (trans {v1.sexpr()} {v2.sexpr()}))")
    def model(self):
        self._cmd("(get-model)")
        buff = last = self._proc.stdout.readline().decode('ascii')
        while last.rstrip() != ')': # TODO find a better way
            last = self._proc.stdout.readline().decode('ascii')
            buff += last
        # if self.debug:
        #     print(f"Got model: {repr(buff)}")
        # Parse the result to make a simple dict
        data = sexpdata.loads(buff)
        res = {}
        for entry in data:
            if type(entry) == sexpdata.Symbol:
                if entry.value() == 'model':
                    # Ok, ostrich likes to say useless things
                    continue
                raise NotImplementedError(f"Weird symbol found in model")
            assert(len(entry) == 5)
            assert(entry[0].value() == 'define-fun')
            v_name = entry[1].value()
            if len(entry[2]) != 0:
                raise NotImplementedError("Sorry can't deal with functions")
            v_type = entry[3].value()
            v_value = entry[4]
            # Ostrich returns some extra values (TODO why ?)
            if v_type == 'RegLan':
                # print("W: RegLan type in model, skipping")
                continue
            if not hasattr(z3, v_type + 'Val'):
                raise NotImplementedError(f"Unknown type {v_type}")
            v_var = getattr(z3, v_type)(v_name)
            if v_value == sexpdata.loads('false'):
                res[v_var] = getattr(z3, v_type + 'Val')(False)
            elif v_value == sexpdata.loads('true'):
                res[v_var] = getattr(z3, v_type + 'Val')(True)
            else:   
                res[v_var] = getattr(z3, v_type + 'Val')(v_value)
        return res
        
    def model_fail(self):
        self._cmd("(get-model)")
        return sexpdata.load(self._proc.stdout)
    
    
    _in_context = False
    @contextmanager
    def context(self):
        """Enter a context whose extra clauses are removed when exited"""
        if self._in_context:
            raise NotImplementedError("Nested context not supported")
        self._in_context = True
        self.push()
        try:
            yield self
        finally:
            self.pop()
            self._in_context = False
class Z3(Z3BasedSolver):
    def __init__(self, path=None, debug=False, silent=True):
        if path is None:
            path = config.get_default_solver_from_config('z3')
        super().__init__(path, debug, silent)
class Z3Noodler(Z3BasedSolver):
    def __init__(self, path=None, 
                 debug=False, 
                 silent=True, 
                 native_auto=False):
        if path is None:
            path = config.get_default_solver_from_config('z3-noodler')
        super().__init__(path, debug, silent, native_auto)
class Z3Alpha(Z3BasedSolver):
    def __init__(self, path=None, 
                 debug=False, 
                 silent=True, 
                 native_auto=False):
        if path is None:
            path = config.get_default_solver_from_config('z3-alpha')
        super().__init__(path, debug, silent, native_auto)
class Ostrich(Z3BasedSolver):
    def __init__(self, path=None,
        debug=False,
        silent=True,
        native_auto=True,
        ):
        if path is None:
            path = config.get_default_solver_from_config('ostrich')
        super().__init__(path, debug, silent, native_auto)
class OstrichFWD(Z3BasedSolver):
    def __init__(self, path=None,
        debug=False,
        silent=True,
        native_auto=True,
        ):
        if path is None:
            path = config.get_default_solver_from_config('ostrich-fwd')
        super().__init__(path, debug, silent, native_auto)
class CVC5(Z3BasedSolver):
    def __init__(self, path=None, debug=False, silent=True):
        if path is None:
            path = config.get_default_solver_from_config('cvc5')
        super().__init__(path, debug, silent)
def test_z3():
    s = Z3()
    x = z3.Int('x')
    y = z3.String('y')
    s.add(z3.Or(x*2 == 84, x == 0))
    s.add(y == "Hello world")
    print(s.check()) # sat
    s.add(x != 0)
    print(s.check()) # sat
    s.push()
    s.add(x != 42)
    print(s.check()) # unsat
    s.pop()
    print(s.check()) # sat again
    print(f"model: {repr(s.model())}")
def test_ostrich():
    s = Ostrich()
    x = z3.String('x')
    s.add(z3.InRe(x, z3.Star(z3.Re("ab"))))
    for i in range(5):
        print(s.check())
        m = s.model()
        print(m)
        s.add(x != m[x])
 
# if __name__ == '__main__':
#     # test_z3()
#     # test_ostrich()
 