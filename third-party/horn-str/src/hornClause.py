import z3
from typing import Set, List, Generator, Optional, Callable, Union, Tuple
import automata

# Assuming HornClauseType is defined somewhere, e.g.:
from enum import Enum

class HornClauseType(Enum):
    INIT = 1
    BLOCK = 2
    INDUCTIVE = 3

class HornClause:
    def __init__(self, c: z3.ExprRef, chc_solver) -> None:
        """
        Construct a HornClause from a given Z3 clause.
        
        Parameters:
          c         : The Z3 formula representing the Horn clause.
          chc_solver: A solver wrapper that provides build_solver, universe, etc.
        """
        self.c = c
        self.chc_solver = chc_solver
        self.vars: Set[z3.ExprRef] = set()
        self.uninterpreted: Set[z3.FuncDeclRef] = set()
        
        # Process quantifiers: remove leading universal quantifiers.
        while isinstance(c, z3.QuantifierRef):
            if not c.is_forall():
                raise NotImplementedError(f"Clause {c} is not supported (only universal quantifiers)")
            body = c.body()
            n = c.num_vars()
            # Z3 uses a reverse order for bound variables: process in descending order.
            for i in range(n):
                idx = n - i - 1  # reverse order
                v_name, v_sort = c.var_name(idx), c.var_sort(idx)
                if v_sort.name() != "String":
                    raise NotImplementedError(f"Unsupported sort {v_sort}")
                var = z3.Const(v_name, v_sort)
                self.vars.add(var)
                # Substitute the bound variable with our named variable.
                body = z3.substitute(body, (z3.Var(i, v_sort), var))
            c = body
        
        # Check that we have an implication in the body.
        if c.decl().name() != '=>':
            raise NotImplementedError(f"Is this a Horn clause? Found: {c}")
        
        left, right = c.children()
        if right.decl().name() == 'not':
            print("W: Not is not implemented yet on the right side")
        elif right.decl().name() == 'false':
            right = None
        elif right.decl().kind() != z3.Z3_OP_UNINTERPRETED:
            raise NotImplementedError(f"Right side {right} should be uninterpreted")

        # Collect uninterpreted predicates from left and right sides.
        self.pre: List[z3.ExprRef] = list(set(self._collect_uninterpreted(left)))
        self.post: List[z3.ExprRef] = list(set(self._collect_uninterpreted(right)))
        
        # Replace uninterpreted predicates in left with True to obtain the condition.
        cond = left
        for up in self.pre:
            cond = z3.substitute(cond, (up, z3.BoolVal(True)))
        self.condition = cond
        
        # Check that there is at least one uninterpreted predicate.
        if len(self.pre + self.post) == 0:
            raise NotImplementedError(f"Cannot deal with clause {c} without uninterpreted predicate")
        # elif max(len(self.pre), len(self.post)) > 1:
        #     print(f"Multiple uninterpreted predicates: pre={self.pre}, post={self.post} in {c}")
            # raise NotImplementedError("More than one uninterpreted predicate should be handled with unification reduction")
        elif not self.pre:
            self.hc_type = HornClauseType.INIT
        elif not self.post:
            self.hc_type = HornClauseType.BLOCK
        else:
            self.hc_type = HornClauseType.INDUCTIVE
        
        # Collect letters (constant characters) from the original formula.
        self.alpha: List[str] = list(set(self._collect_letters(self.c)))
        
        # Save the input and output variables if applicable.
        self.varin = self.varout = None
        if self.pre:
            self.varin = self.pre[0].children()
        if self.post:
            self.varout = self.post[0].children()

    def __str__(self) -> str:
        return f"{self.hc_type.name}: cond: {self.condition}, {self.pre} => {self.post}"

    def _collect_uninterpreted(self, f: Optional[z3.ExprRef], allowed: bool = True) -> Generator[z3.ExprRef, None, None]:
        """
        Recursively collect uninterpreted predicates from the formula.
        
        Parameters:
          f       : The Z3 expression (or None).
          allowed : Whether uninterpreted predicates under negation are allowed.
        
        Yields:
          Z3 expressions corresponding to uninterpreted predicates.
        """
        if f is None:
            return
        
        # If f has children, recursively process them.
        if hasattr(f, 'children'):
            try:
                if f.decl().name() == 'not':
                    allowed = False
            except z3.Z3Exception:
                pass
            for child in f.children():
                yield from self._collect_uninterpreted(child, allowed=allowed)
        
        # Also process the body of quantifiers.
        if hasattr(f, 'body'):
            yield from self._collect_uninterpreted(f.body())
        
        try:
            decl = f.decl()
        except z3.Z3Exception:
            return
        
        if decl.kind() == z3.Z3_OP_UNINTERPRETED:
            # Handle constant uninterpreted predicates (arity 0).
            if decl.arity() == 0:
                if z3.Const(decl.name(), decl.range()) not in self.vars:
                    raise NotImplementedError(f"Free variable {decl.name()}?")
                return
            
            # Check that we support the domain and range (here: String -> Bool).
            # d = decl.domain()
            # r = decl.range()
            # if d.name() != "String" or r.name() != "Bool":
                # raise NotImplementedError(f"{f}: Expected sort String->Bool but got {d}->{r}")
            
            fct = z3.Function(decl.name(), *(decl.domain(i) for i in range(decl.arity())), decl.range())
            if fct not in self.uninterpreted:
                self.uninterpreted.add(fct)
            yield f

    def _collect_letters(self, f: Optional[z3.ExprRef]) -> Generator[str, None, None]:
        """
        Recursively collect all constant letters (string values) appearing in the formula.
        """
        if f is None:
            return
        if hasattr(f, 'children'):
            for child in f.children():
                yield from self._collect_letters(child)
        if hasattr(f, 'is_string_value') and f.is_string_value():
            yield from f.as_string()

    def build_solver(self, negate: bool = False, varout: Optional[z3.ExprRef] = None, mem: bool = False) -> z3.Solver:
        """
        Build and return a solver for the clause's condition.
        
        Parameters:
          negate: If True, add the negation of the condition.
          varout: If provided, add a constraint that varout is in the universe.
          mem   : Passes the memory flag to chc_solver.build_solver.
        """
        s = self.chc_solver.build_solver(mem=mem)
        if varout is not None:
            s.add(z3.InRe(varout, self.chc_solver.universe))
        if negate:
            s.add(z3.Not(self.condition))
        else:
            s.add(self.condition)
        return s

    def generate_formula(self, negate: bool = False, varout: Optional[z3.ExprRef] = None, mem: bool = False) -> z3.ExprRef:
        """
        Generate the underlying formula (without creating a solver).
        
        Parameters:
          negate: If True, return the negated condition.
          varout: If provided, add the universe membership constraint for varout.
          mem   : (Not used directly here but kept for API consistency.)
        """
        parts = []
        if varout is not None:
            parts.append(z3.InRe(varout, self.chc_solver.universe))
        parts.append(z3.Not(self.condition) if negate else self.condition)
        # Combine constraints with AND if more than one.
        return z3.And(parts) if len(parts) > 1 else parts[0]

    def is_length_preserving(self) -> bool:
        """
        Check if the Horn clause is length preserving.
        For inductive clauses, this means that the lengths of varin and varout are equal.
        """
        if self.hc_type != HornClauseType.INDUCTIVE:
            return True
        
        solver = self.build_solver()
        va = self.pre[0].children()[0]
        vb = self.post[0].children()[0]
        solver.add(z3.Length(va) != z3.Length(vb))
        res = solver.check()
        if res == z3.unsat:
            return True
        elif res == z3.sat:
            return False
        else:
            raise NotImplementedError("Cannot determine if the clause is length-preserving")

    def build_membership_oracle(self) -> Callable[[str], bool]:
        """
        Build and return a membership oracle function that checks if a word is in the set.
        Only applicable to INIT and BLOCK clauses.
        """
        if self.hc_type == HornClauseType.INDUCTIVE:
            raise NotImplementedError("Membership oracle not available for inductive clauses")
        
        var = self.post[0].children()[0] if self.hc_type == HornClauseType.INIT else self.pre[0].children()[0]
        solver = self.build_solver(mem=True)
        
        def mem(w: str) -> bool:
            # Use a solver context to avoid polluting the global state.
            with solver.context():
                solver.add(var == z3.StringVal(w))
                res = solver.check()
                if res == z3.unknown:
                    raise NotImplementedError(f"Cannot check membership for {w}")
                return res == z3.sat
        
        return mem

    def build_transition_oracle(self, post: bool = True) -> Callable[[str], Generator[str, None, None]]:
        """
        Build a transition oracle returning all successors (if post=True) or all predecessors (if post=False)
        for inductive clauses.
        """
        if self.hc_type != HornClauseType.INDUCTIVE:
            raise NotImplementedError("Transition oracle is only applicable for inductive clauses")
        
        # Choose variables based on whether we want successors or predecessors.
        varin = self.varin if post else self.varout
        varout = self.varout if post else self.varin

        # TODO: take care of the lstar case
        if len(varin) > 0:
            varin = varin[0]
        if len(varout) > 0:
            varout = varout[0]

        def gen(w: str) -> Generator[str, None, None]:
            solver = self.build_solver(varout=varout, mem=True)
            solver.add(varin == z3.StringVal(w))
            while True:
                res = solver.check()
                if res == z3.unsat:
                    break
                if res == z3.unknown:
                    raise NotImplementedError(f"Cannot process transition for {w}")
                model = solver.model()
                out_val = model[varout]
                out_str = out_val.as_string()
                yield out_str
                # Exclude the found value and search for more.
                solver.add(varout != out_val)
        
        return gen

    def build_set_oracle(self) -> Callable[[int], Generator[str, None, None]]:
        """
        Build a set oracle returning all words of a given length satisfying the clause.
        Only applicable to INIT and BLOCK clauses.
        """
        if self.hc_type == HornClauseType.INDUCTIVE:
            raise NotImplementedError("Set oracle not available for inductive clauses")
        
        var = self.post[0].children()[0] if self.hc_type == HornClauseType.INIT else self.pre[0].children()[0]
        solver = self.build_solver(varout=var, mem=True)
        
        def gen(n: int) -> Generator[str, None, None]:
            with solver.context():
                # You may choose one of the following constraints:
                # Option 1: Use native length constraint.
                # solver.add(z3.Length(var) == n)
                # Option 2: Use an automata-based constraint.
                auto = automata.MatrixNFA(
                    init=[0],
                    acc=[n],
                    mat=[{a: [i+1] for a in self.chc_solver.alpha} for i in range(n)] + [{}]
                )
                solver.add_word_membership(var, auto)
                while True:
                    res = solver.check()
                    if res == z3.unsat:
                        break
                    if res == z3.unknown:
                        raise NotImplementedError(f"Cannot enumerate words of length {n}")
                    model = solver.model()
                    word = model[var].as_string()
                    yield word
                    solver.add(var != model[var])
        
        return gen

    def build_equiv_check(self) -> Callable[[any], Optional[Union[str, Tuple[str, str]]]]:
        """
        Build an equivalence checker that, given an automaton, checks if the automaton
        satisfies the Horn clause. If the automaton satisfies the clause, returns None;
        otherwise returns a counterexample (either a single word or a pair for inductive clauses).
        
        The underlying clause is of the form:
           φ(varin) /\ C(varin, varout) => φ(varout)
        """
        # We use either varin or varout as the bound variable.
        bound = self.varin if self.varin is not None else self.varout
        solver = self.build_solver(varout=bound)
        
        def equiv(auto) -> Optional[Union[str, Tuple[str, str]]]:
            with solver.context():
                # If we have a pre-condition, constrain varin to be in the automaton's language.
                if self.varin is not None:
                    solver.add_word_membership(self.varin, auto)
                # For the post-condition, add the negation (i.e., look for a counterexample).
                if self.varout is not None:
                    solver.add_word_membership(self.varout, auto, negate=True)
                
                res = solver.check()
                if res == z3.unknown:
                    raise NotImplementedError("Cannot check equivalence")
                if res == z3.unsat:
                    return None  # The automaton satisfies the clause.
                
                model = solver.model()
                cex1 = model[self.varin].as_string() if self.varin is not None else None
                cex2 = model[self.varout].as_string() if self.varout is not None else None
                
                if cex1 is not None and cex2 is not None:
                    return (cex1, cex2)
                return cex1 if cex1 is not None else cex2
        
        return equiv
