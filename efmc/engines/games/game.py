#!/usr/bin/python3

import re, logging
# from six.moves import cStringIO
from pysmt.shortcuts import *
from pysmt.parsing import parse
from pysmt.smtlib.parser import SmtLibParser


# from subprocess import Popen, PIPE


class Game:

    def solve(self, n):

        # Initialize result and dynamic init variable
        result = FALSE()
        new_init = self.init
        self.print_debug('New Subgame')
        self.print_debug('New init', new_init)
        self.print_debug('New goal', self.goal)

        # Intersect init and goal, check whether there are init state that are not goal
        if is_sat(And(new_init, self.goal), solver_name='msat'):
            # There are states that are init and goal, update result
            result = And(new_init, self.goal)
            if is_unsat(And(new_init, Not(self.goal)), solver_name='msat'):
                # init subsetminus goal is empty, we can stop computation
                self.print_debug(descr='Return', formula=new_init)
                # it holds that (new_init -> goal)
                return new_init, n + 1
            else:
                # init subsetminus goal is not empty, continue computation with new dynamic init
                new_init = And(new_init, Not(self.goal)).simplify()

        # Use specified interpolation procedure
        # it seems that to use the interpolant API in pysmt, we need to install mathsat?
        interpolant = self.interpolate(new_init, self.goal)

        necessary_reach = self.instantiate(self.reach, interpolant).simplify()
        necessary_safe = self.instantiate(self.safe, interpolant).simplify()
        self.print_debug(descr='Interpolant', formula=interpolant)

        # Check whether SAFE controls the necessary subgoal in stages
        if is_unsat(necessary_reach, solver_name='msat'):
            self.print_debug(descr='no reach')

            # REACH has no moves through the subgoal, check partial CPre of SAFE (we can keep quantifiers here if we use z3)
            controlled_safe = And(necessary_safe, Not(Exists(self.next.values(),
                                                             And(self.safe, Not(interpolant).substitute(self.next)))))
            if is_unsat(controlled_safe, solver_name='z3'):
                # CPre at the interpolant slice is empty, it follows that SAFE has a strategy here and we stop
                self.print_debug(descr='Return', formula=result)
                return result, n + 1
            else:
                necessary_subgoal = necessary_safe
                self.print_debug(descr='safe cant control')
        else:
            # REACH has moves through the subgoal, simply continue with full subgoal
            necessary_subgoal = Or(necessary_reach, necessary_safe)

        self.print_debug(descr='Necessary subgoal', formula=necessary_subgoal)

        # Solve restricted game starting in the successor states of the subgoal
        first_subgame = Game(self.next,
                             self.post_project(necessary_subgoal).substitute(self.prev),
                             And(self.safe, interpolant),
                             And(self.reach, interpolant),
                             self.goal,
                             self.depth + 1,
                             self.id + '.0')
        bad_states, n_first = first_subgame.solve(n)

        # Check which subset of the sufficient subgoal can ensure the post-condition
        f = self.enforcable(And(necessary_subgoal, bad_states.substitute(self.next)))
        # Eliminate Quantifiers and primed variables
        pre_f = self.pre_project(f)

        # Check sufficient and enforcable subgoal for emptiness
        if is_unsat(pre_f, solver_name='msat'):
            self.print_debug(descr='Return', formula=result)
            return result, n_first + 1

        # Check whether safety player can escape the restricted subgame
        if is_sat(And(Or(self.safe, self.reach), interpolant, Not(self.goal), Not(interpolant.substitute(self.next)))):
            # If he can escape use the union of goal and pre_f to ensure we keep a necessary subgoal
            f = self.enforcable(And(Or(self.safe, self.reach), Or(bad_states, self.goal).substitute(self.next)))
            pre_f = self.pre_project(f)
            second_subgame = Game(self.next,
                                  new_init.simplify(),
                                  And(self.safe, Not(Or(bad_states, self.goal).substitute(self.next))).simplify(),
                                  And(self.reach, Not(Or(bad_states, self.goal).substitute(self.next))).simplify(),
                                  pre_f.simplify(),
                                  self.depth + 1,
                                  self.id + '.1')

        else:
            # If he cannot escape, pre_f fully qualifies as necessary subgoal already
            second_subgame = Game(self.next,
                                  new_init.simplify(),
                                  And(self.safe, Not(interpolant),
                                      Not(And(necessary_subgoal, bad_states.substitute(self.next)))).simplify(),
                                  And(self.reach, Not(interpolant),
                                      Not(And(necessary_subgoal, bad_states.substitute(self.next)))).simplify(),
                                  pre_f.simplify(),
                                  self.depth + 1,
                                  self.id + '.1')

        # Reach wins from those initial states that reach the computed necessary and sufficient subgoal
        subset, n_last = second_subgame.solve(n_first)
        self.print_debug(descr='Return', formula=Or(result, subset))
        return Or(result, subset), n_last + 1

    def interpolate(self, a, b):
        """
        Computes Craig interpolant between a and b.

        Parameters:
        a (FNode) -- Left operand of interpolation;
        b (FNode) -- Right operand of interpolation.

        Returns:
        (FNode) -- Craig interpolant between a and b.
        """
        b_np = qelim(Exists([Symbol('r', BOOL)], b))
        a_np = qelim(Exists([Symbol('r', BOOL)], a))

        if is_unsat(And(a_np, b_np)):
            self.print_debug('Abstracted r interpolant')
            return binary_interpolant(b_np, a_np, solver_name='msat')
        else:
            self.print_debug('r interpolant')
            return binary_interpolant(b, a, solver_name='msat')

    def instantiate(self, t, phi):
        """
        Instantiates all transitions bridging interpolant phi.

        Parameters:
        t (FNode) -- Full (both safe and reach) transition relation;
        phi (FNode) -- Interpolant phi.

        Returns:
        (FNode) -- All transitions bridging phi, i.e., And(t,phi,Not(phi')).
        """
        return And(t, Not(phi), phi.substitute(self.next))

    def enforcable(self, phi):
        """
        For some set of transitions phi, returns the transitions that can be enforced by the reachability player

        Parameters:
        phi (FNode) -- Predicate characterizing the set of transitions.

        Returns:
        (FNode) -- Subset of phi that can be enforced by REACH in the predecessor states.
        """
        return And(phi, Not(Exists(self.next.values(), And(self.safe, Not(phi)))))

    def cpre(self, phi):
        """
        Applies the controlled predecessor operator starting from phi.
        Eliminates quantifiers and simplifies on return.

        Parameters:
        phi (FNode) -- Predicate characterizing the set of goal states.

        Returns:
        (FNode) -- Controlled predecessor, i.e., Qelim(Forall safe -> phi Or Exists reach /\ phi).
        """
        p = phi.substitute(self.next)
        safe_forall = And(self.pre_project(self.safe), Not(Exists(self.next.values(), And(self.safe, Not(p)))))
        reach_exists = Exists(self.next.values(), And(self.reach, p))
        cpre = Or(safe_forall, reach_exists).simplify()
        self.print_debug(descr='Cpre', formula=cpre)
        c = qelim(cpre, solver_name='msat_lw')
        self.print_debug(descr='Finished qelim')
        return c

    def pre_project(self, phi):
        """
        Projects the formula onto the normal/prev variables by abstracting the primed/next variables.
        Applies an existential quantifier to abstract the primed variables and eliminates it after.

        Parameters:
        phi (FNode) -- Formula to be projected.

        Returns:
        (FNode) -- Qelim(Exists[X].F).
        """
        r = Exists(self.next.values(), phi)
        res = qelim(r, solver_name='msat_lw')
        return res

    def post_project(self, phi):
        """
        Projects the formula onto the primed/next variables by abstracting the normal/prev variables.
        Applies an existential quantifier to abstract the prev variables and eliminates it after.

        Parameters:
        phi (FNode) -- Formula to be projected.

        Returns:
        (Fnode) -- Qelim(Exists[x].F).
        """
        r = Exists(self.prev.values(), phi)
        res = qelim(r, solver_name='msat_lw')
        return res

    @classmethod
    def read(cls, filename):
        """
        Reads in the reachability game from a given file.

        Parameters:
        filename (.rg file) -- Game description in rg-format.

        Returns:
        (Game) -- Game in PySMT description (alters formulas to enforce alternation).
        """
        with open(filename) as file:
            contents = file.read()
        tokens = re.split('\n|:', contents)
        mode = ''
        ints = []
        bools = []
        reals = []
        init = ''
        safe = ''
        reach = ''
        goal = ''
        modes = re.compile('int|bool|real|init|safe|reach|goal')
        for tok in tokens:
            t = tok.rstrip()
            if modes.match(t):
                mode = t
            else:
                if mode == 'int':
                    ints.extend(re.split(',|\[|\]', t.replace(' ', '')))
                if mode == 'bool':
                    bools.extend(re.split(',', t.replace(' ', '')))
                if mode == 'real':
                    reals.extend(re.split(',|\[|\]', t.replace(' ', '')))
                elif mode == 'init':
                    init += t
                elif mode == 'safe':
                    safe += t
                elif mode == 'reach':
                    reach += t
                elif mode == 'goal':
                    goal += t

        # Handle boolean variables (implicitly bounded)
        bools.append('r')
        bool_next = {Symbol(v, BOOL): Symbol(v.upper(), BOOL) for v in bools}
        # Parse integer variables (might be bounded)
        var_int, bnd_int = parse_bounds(ints, INT)
        int_next = {v: Next(v) for v in var_int}
        # Parse real variables (might be bounded)
        var_real, bnd_real = parse_bounds(reals, REAL)
        real_next = {v: Next(v) for v in var_real}
        # Merge int and real
        nexts = {**int_next, **bool_next, **real_next}
        bnds = And(bnd_int + bnd_real)

        alt_init = And(parse(init), Iff(Symbol('r', BOOL), Bool(False)), bnds)
        alt_safe = And(parse(safe), Iff(Symbol('r', BOOL), Bool(False)), Iff(Symbol('R', BOOL), Bool(True)), bnds,
                       bnds.substitute(nexts))
        alt_reach = And(parse(reach), Iff(Symbol('r', BOOL), Bool(True)), Iff(Symbol('R', BOOL), Bool(False)), bnds,
                        bnds.substitute(nexts))
        alt_goal = And(parse(goal), Iff(Symbol('r', BOOL), Bool(False)), bnds)
        return Game(nexts, alt_init, alt_safe, alt_reach, alt_goal)

    def print_debug(self, descr, formula=None):
        if logging.DEBUG >= logging.root.level:
            if formula is None:
                logging.debug(self.depth * '>' + descr + '(' + self.id + ')')
            else:
                logging.debug(self.depth * '>' + descr + '(' + self.id + ')' + ':' + '%s' % formula.serialize(
                    self.formula_print_depth))

    def __init__(self, var_next, init, safe, reach, goal, depth=0, id='0'):
        self.next = var_next
        self.prev = {n: v for v, n in self.next.items()}
        self.init = init
        self.safe = safe
        self.reach = reach
        self.goal = goal
        self.parser = SmtLibParser()
        self.depth = depth
        self.id = id
        self.formula_print_depth = 10


def Next(v):
    """
    Returns the next/primed version of a variable.

    Parameters:
    v (Symbol) -- variable to be primed.

    Returns:
    (Symbol) -- primed variable.
    """
    return Symbol(v.symbol_name().upper(), v.symbol_type())


def parse_bounds(tokens, typ):
    """
    Parses a list of variable tokens with optional value intervals.

    Parameters:
    tokens ([string]) -- token list;
    typ (INT/REAL) -- type of the variables.

    Returns:
    var ([Symbol]) -- list of variables;
    bnds ([FNode]) -- list of bound constraints.
    """
    bnds = []
    var = []
    lower = ''
    for t in tokens:
        if str.isalpha(t):
            var.append(Symbol(t, typ))
        else:
            if lower == '':
                lower = t
            else:
                if typ == INT:
                    bnds.append(GE(var[-1], Int(int(lower))))
                    bnds.append(LE(var[-1], Int(int(t))))
                elif typ == REAL:
                    bnds.append(GE(var[-1], Real(float(lower))))
                    bnds.append(LE(var[-1], Real(float(t))))
                lower = ''
    return var, bnds
