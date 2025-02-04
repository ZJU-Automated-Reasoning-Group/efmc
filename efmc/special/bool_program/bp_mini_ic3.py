"""
Verifying Boolean programs using IC3

 TODO: This file is taken from the examples of Z3' codebase.
  We should modify it for accepting Boolean transition systems
"""
import heapq
import sys

import z3


# Simplistic (and fragile) converter from
# a class of Horn clauses corresponding to
# a transition system into a transition system
# representation as <init, trans, goal>
# It assumes it is given three Horn clauses
# of the form:
#  init(x) => Invariant(x)
#  Invariant(x) and trans(x,x') => Invariant(x')
#  Invariant(x) and goal(x) => Goal(x)
# where Invariant and Goal are uninterpreted predicates


class Horn2Transitions:
    def __init__(self):
        self.trans = True
        self.init = True
        self.inputs = []
        self.goal = True
        self.index = 0

    def parse(self, file):
        fp = z3.Fixedpoint()
        goals = fp.parse_file(file)
        for r in fp.get_rules():
            if not z3.is_quantifier(r):
                continue
            b = r.body()
            if not z3.is_implies(b):
                continue
            f = b.arg(0)
            g = b.arg(1)
            if self.is_goal(f, g):
                continue
            if self.is_transition(f, g):
                continue
            if self.is_init(f, g):
                continue

    def is_pred(self, p, name):
        return z3.is_app(p) and p.decl().name() == name

    def is_goal(self, body, head):
        if not self.is_pred(head, "Goal"):
            return False
        pred, inv = self.is_body(body)
        if pred is None:
            return False
        self.goal = self.subst_vars("x", inv, pred)
        self.goal = self.subst_vars("i", self.goal, self.goal)
        self.inputs += self.vars
        self.inputs = list(set(self.inputs))
        return True

    def is_body(self, body):
        if not z3.is_and(body):
            return None, None
        fmls = [f for f in body.children() if self.is_inv(f) is None]
        inv = None
        for f in body.children():
            if self.is_inv(f) is not None:
                inv = f
                break
        return z3.And(fmls), inv

    def is_inv(self, f):
        if self.is_pred(f, "Invariant"):
            return f
        return None

    def is_transition(self, body, head):
        pred, inv0 = self.is_body(body)
        if pred is None:
            return False
        inv1 = self.is_inv(head)
        if inv1 is None:
            return False
        pred = self.subst_vars("x", inv0, pred)
        self.xs = self.vars
        pred = self.subst_vars("xn", inv1, pred)
        self.xns = self.vars
        pred = self.subst_vars("i", pred, pred)
        self.inputs += self.vars
        self.inputs = list(set(self.inputs))
        self.trans = pred
        return True

    def is_init(self, body, head):
        for f in body.children():
            if self.is_inv(f) is not None:
                return False
        inv = self.is_inv(head)
        if inv is None:
            return False
        self.init = self.subst_vars("x", inv, body)
        return True

    def subst_vars(self, prefix, inv, fml):
        subst = self.mk_subst(prefix, inv)
        self.vars = [v for (k, v) in subst]
        return z3.substitute(fml, subst)

    def mk_subst(self, prefix, inv):
        self.index = 0
        if self.is_inv(inv) is not None:
            return [(f, self.mk_bool(prefix)) for f in inv.children()]
        else:
            all_vars = self.get_vars(inv)
            return [(f, self.mk_bool(prefix)) for f in all_vars]

    def mk_bool(self, prefix):
        self.index += 1
        return z3.Bool("%s%d" % (prefix, self.index))

    def get_vars(self, f, rs=[]):
        if z3.is_var(f):
            return z3.z3util.vset(rs + [f], str)
        else:
            for f_ in f.children():
                rs = self.get_vars(f_, rs)
            return z3.z3util.vset(rs, str)


# Produce a finite domain solver.
# The theory QF_FD covers bit-vector formulas
# and pseudo-Boolean constraints.
# By default cardinality and pseudo-Boolean
# constraints are converted to clauses. To override
# this default for cardinality constraints
# we set sat.cardinality.solver to True

def fd_solver():
    s = z3.SolverFor("QF_FD")
    s.set("sat.cardinality.solver", True)
    return s


# negate, avoid double negation
def negate(f):
    if z3.is_not(f):
        return f.arg(0)
    else:
        return z3.Not(f)


def cube2clause(cube):
    return z3.Or([negate(f) for f in cube])


class State:
    def __init__(self, s):
        self.R = set([])
        self.solver = s

    def add(self, clause):
        if clause not in self.R:
            self.R |= {clause}
            self.solver.add(clause)


class Goal:
    def __init__(self, cube, parent, level):
        self.level = level
        self.cube = cube
        self.parent = parent

    def __lt__(self, other):
        return self.level < other.level


def is_seq(f):
    return isinstance(f, list) or isinstance(f, tuple) or isinstance(f, z3.AstVector)


# Check if the initial state is bad
def check_disjoint(a, b):
    s = fd_solver()
    s.add(a)
    s.add(b)
    return z3.unsat == s.check()


# Remove clauses that are subsumed
def prune(R):
    removed = set([])
    s = fd_solver()
    for f1 in R:
        s.push()
        for f2 in R:
            if f2 not in removed:
                s.add(z3.Not(f2) if f1.eq(f2) else f2)
        if s.check() == z3.unsat:
            removed |= {f1}
        s.pop()
    return R - removed


class MiniIC3:
    def __init__(self, init, trans, goal, x0, inputs, xn):
        self.x0 = x0
        self.inputs = inputs
        self.xn = xn
        self.init = init
        self.bad = goal
        self.trans = trans
        self.min_cube_solver = fd_solver()
        self.min_cube_solver.add(z3.Not(trans))
        self.goals = []
        s = State(fd_solver())
        s.add(init)
        s.solver.add(trans)
        self.states = [s]
        self.s_bad = fd_solver()
        self.s_good = fd_solver()
        self.s_bad.add(self.bad)
        self.s_good.add(z3.Not(self.bad))

    def next(self, f):
        if is_seq(f):
            return [self.next(f1) for f1 in f]
        return z3.substitute(f, [p for p in zip(self.x0, self.xn)])

    def prev(self, f):
        if is_seq(f):
            return [self.prev(f1) for f1 in f]
        return z3.substitute(f, [p for p in zip(self.xn, self.x0)])

    def add_solver(self):
        s = fd_solver()
        s.add(self.trans)
        self.states += [State(s)]

    def R(self, i):
        return z3.And(self.states[i].R)

    # Check if there are two states next to each other that have the same clauses.
    def is_valid(self):
        i = 1
        while i + 1 < len(self.states):
            if not (self.states[i].R - self.states[i + 1].R):
                return z3.And(prune(self.states[i].R))
            i += 1
        return None

    def value2literal(self, m, x):
        value = m.eval(x)
        if z3.is_true(value):
            return x
        if z3.is_false(value):
            return z3.Not(x)
        return None

    def values2literals(self, m, xs):
        p = [self.value2literal(m, x) for x in xs]
        return [x for x in p if x is not None]

    def project0(self, m):
        return self.values2literals(m, self.x0)

    def projectI(self, m):
        return self.values2literals(m, self.inputs)

    def projectN(self, m):
        return self.values2literals(m, self.xn)

    # Determine if there is a cube for the current state
    # that is potentially reachable.
    def unfold(self):
        core = []
        self.s_bad.push()
        R = self.R(len(self.states) - 1)
        self.s_bad.add(R)
        is_sat = self.s_bad.check()
        if is_sat == z3.sat:
            m = self.s_bad.model()
            cube = self.project0(m)
            props = cube + self.projectI(m)
            self.s_good.push()
            self.s_good.add(R)
            is_sat2 = self.s_good.check(props)
            assert is_sat2 == z3.unsat
            core = self.s_good.unsat_core()
            core = [c for c in core if c in set(cube)]
            self.s_good.pop()
        self.s_bad.pop()
        return is_sat, core

    # Block a cube by asserting the clause corresponding to its negation
    def block_cube(self, i, cube):
        self.assert_clause(i, cube2clause(cube))

    # Add a clause to levels 0 until i
    def assert_clause(self, i, clause):
        for j in range(i + 1):
            self.states[j].add(clause)

    # minimize cube that is core of Dual solver.
    # this assumes that props & cube => Trans
    def minimize_cube(self, cube, inputs, lits):
        is_sat = self.min_cube_solver.check(lits + [c for c in cube] + [i for i in inputs])
        assert is_sat == z3.unsat
        core = self.min_cube_solver.unsat_core()
        assert core
        return [c for c in core if c in set(cube)]

    # push a goal on a heap
    def push_heap(self, goal):
        heapq.heappush(self.goals, (goal.level, goal))

    # A state s0 and level f0 such that
    # not(s0) is f0-1 inductive
    def ic3_blocked(self, s0, f0):
        self.push_heap(Goal(self.next(s0), None, f0))
        while self.goals:
            f, g = heapq.heappop(self.goals)
            sys.stdout.write("%d." % f)
            sys.stdout.flush()
            # Not(g.cube) is f-1 invariant
            if f == 0:
                print("")
                return g
            cube, f, is_sat = self.is_inductive(f, g.cube)
            if is_sat == z3.unsat:
                self.block_cube(f, self.prev(cube))
                if f < f0:
                    self.push_heap(Goal(g.cube, g.parent, f + 1))
            elif is_sat == z3.sat:
                self.push_heap(Goal(cube, g, f - 1))
                self.push_heap(g)
            else:
                return is_sat
        print("")
        return None

    # Rudimentary generalization:
    # If the cube is already unsat with respect to transition relation
    # extract a core (not necessarily minimal)
    # otherwise, just return the cube.
    def generalize(self, cube, f):
        s = self.states[f - 1].solver
        if z3.unsat == s.check(cube):
            core = s.unsat_core()
            if not check_disjoint(self.init, self.prev(z3.And(core))):
                return core, f
        return cube, f

    # Check if the negation of cube is inductive at level f
    def is_inductive(self, f, cube):
        s = self.states[f - 1].solver
        s.push()
        s.add(self.prev(z3.Not(z3.And(cube))))
        is_sat = s.check(cube)
        if is_sat == z3.sat:
            m = s.model()
        s.pop()
        if is_sat == z3.sat:
            cube = self.next(self.minimize_cube(self.project0(m), self.projectI(m), self.projectN(m)))
        elif is_sat == z3.unsat:
            cube, f = self.generalize(cube, f)
        return cube, f, is_sat

    def run(self):
        if not check_disjoint(self.init, self.bad):
            return "goal is reached in initial state"
        level = 0
        while True:
            inv = self.is_valid()
            if inv is not None:
                return inv
            is_sat, cube = self.unfold()
            if is_sat == z3.unsat:
                level += 1
                print("Unfold %d" % level)
                sys.stdout.flush()
                self.add_solver()
            elif is_sat == z3.sat:
                cex = self.ic3_blocked(cube, level)
                if cex is not None:
                    return cex
            else:
                return is_sat


def test(file):
    h2t = Horn2Transitions()
    h2t.parse(file)
    mp = MiniIC3(h2t.init, h2t.trans, h2t.goal, h2t.xs, h2t.inputs, h2t.xns)
    result = mp.run()
    if isinstance(result, Goal):
        g = result
        print("Trace")
        while g:
            print(g.level, g.cube)
            g = g.parent
        return
    if isinstance(result, z3.ExprRef):
        print("Invariant:\n%s " % result)
        return
    print(result)


test("../../benchmarks/chc/bool/horn4.smt2")
# test("data/horn2.smt2")
# test("data/horn3.smt2")
# test("data/horn4.smt2")
# test("data/horn5.smt2")
# test("data/horn6.smt2") # takes long time to finish
