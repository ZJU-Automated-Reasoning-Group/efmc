"""
Transition system (Abstraction of programs)
"""

from typing import List

import z3

from efmc.utils import ctx_simplify


class TransitionSystem(object):
    """
    TODO: This is a trivial transition system with several restrictions
       1. Only one invariant
       2. Number of self.variables and self.prime_variables are the same
       3. All variables in self.variables have the same type, e.g., real/int
      We should break these restrictions to support more programs.
    """

    def __init__(self, *args, **kwargs):
        # Default initialization
        self.all_variables = []  # self.variables + self.prime_variables
        self.variables = []  # x, y
        self.prime_variables = []  # x!, y!
        self.trans = None  # formula about the relation of x, y, x!, y!
        self.init = None  # formula about x, y
        self.post = None  # formula about x, y
        self.invariants = []  # list of additional invariants/lemmas (which can be specified by the user or inferred)
        self.initialized = False

        self.has_bv = False
        self.signedness = "unsigned"

        self.has_int = False
        self.has_real = False
        self.has_array = False
        self.has_bool = False

        # Handle keyword arguments if provided
        if kwargs:
            self._init_from_kwargs(**kwargs)

    def _init_from_kwargs(self, **kwargs):
        """Initialize the transition system from keyword arguments."""
        allowed_keys = {'variables', 'prime_variables', 'init', 'trans', 'post', 'invariants'}
        for key, value in kwargs.items():
            if key not in allowed_keys:
                raise ValueError(f"Unexpected argument: {key}")
            if key == 'variables':
                self.variables = list(value)
            elif key == 'prime_variables':
                self.prime_variables = list(value)
            elif key == 'init':
                self.init = value
            elif key == 'trans':
                self.trans = value
            elif key == 'post':
                self.post = value
            elif key == 'invariants':
                self.invariants = list(value) if isinstance(value, (list, tuple)) else [value]

        # Update all_variables after setting variables and prime_variables
        self.all_variables = self.variables + self.prime_variables

        # FIXME: currently, we assume that all variables are of the same type.
        #  thus, we use the first variable to decide the type. However, this
        #  is not a good idea. At least, we should suppor the mix of 
        #  int/bv/real and bool, which is reasonable...
        sample_var = self.variables[0]
        # print(sample_var.sort())
        if z3.is_int(sample_var):
            self.has_int = True
        elif z3.is_real(sample_var):
            self.has_real = True
        elif z3.is_bv(sample_var):
            self.has_bv = True
        elif z3.is_bool(sample_var):
            self.has_bool = True
        else:
            # FIXME: it should be easy to handle handle
            #  Boolean variables?
            raise NotImplementedError

        self.initialized = True

    def set_signedness(self, ty: str):
        assert self.has_bv
        if ty == "signed":
            self.signedness = "signed"
        elif ty == "unsigned":
            self.signedness = "unsigned"
        else:
            raise NotImplementedError

    def add_post(self, exp):
        """Update/initialize set.post (to be verified)"""
        self.post = exp

    def __repr__(self):
        print(self.all_variables)
        print(self.init)
        print(self.trans)
        print(self.post)
        return " "

    def from_z3_cnts(self, ts: List):
        """A trick for initializing sts"""
        self.all_variables, self.init, self.trans, self.post = ts[0], ts[1], ts[2], ts[3]
        # print(self.all_variables)
        for var in self.all_variables:
            # print(str(var))
            # FIXME: using name is not a good and general idea
            if str(var).endswith("!") or str(var).endswith("'"):
                self.prime_variables.append(var)
            else:
                self.variables.append(var)
        # print(self.variables, self.prime_variables)

        # FIXME: currently, we assume that each variable has the same type
        #  However, we may want to support sts that has different types of variables.
        sample_var = self.variables[0]
        # print(sample_var.sort())
        if z3.is_int(sample_var):
            self.has_int = True
        elif z3.is_real(sample_var):
            self.has_real = True
        elif z3.is_bv(sample_var):
            self.has_bv = True
        elif z3.is_bool(sample_var):
            self.has_bool = True
        else:
            raise NotImplementedError

        self.initialized = True
        # self.analyze_and_simplify() # is this OK?

    def analyze_and_simplify(self):
        """Simplify the problem?"""
        self.trans = ctx_simplify(self.trans)  # ctx_simplify can be slow

    def to_chc_constraints(self) -> z3.ExprRef:
        """
        FIXME: Other APIs will this function to serialize the transition system to CHC constraints.
        
        However, using Z3's sovle obect to dump may not be a good idea, since it may create the let expresion, for which our simplified CHC parser may not work. Besides, other third-party SMT solvers may not support some extensions of Z3.
        """
        if self.has_array:
            raise NotImplementedError

        s = z3.SolverFor("HORN")
        inv_sig = "z3.Function(\'inv\', "

        if self.has_int:
            for _ in range(len(self.variables)): inv_sig += "z3.IntSort(), "
        elif self.has_real:
            for _ in range(len(self.variables)): inv_sig += "z3.RealSort(), "
        elif self.has_bv:
            bv_size = self.variables[0].sort().size()
            for _ in range(len(self.variables)): inv_sig += "z3.BitVecSort({}), ".format(str(bv_size))
        elif self.has_bool:
            for _ in range(len(self.variables)): inv_sig += "z3.BoolSort(), "
        else:
            raise NotImplementedError

        inv_sig += "z3.BoolSort())"
        inv = eval(inv_sig)
        # Init
        s.add(z3.ForAll(self.variables, z3.Implies(self.init,
                                                   inv(self.variables))))
        # Inductive
        s.add(z3.ForAll(self.all_variables, z3.Implies(z3.And(inv(self.variables), self.trans),
                                                       
                                                       inv(self.prime_variables))))
        # Post
        s.add(z3.ForAll(self.variables, z3.Implies(inv(self.variables),
                                                   self.post)))

        return z3.And(s.assertions())

    def to_chc_str(self) -> str:
        """Convert to CHC format
        """
        assert self.initialized
        z3_expr = self.to_chc_constraints()
        return "(set-logic HORN)\n" + z3_expr.sexpr() + "\n(check-sat)\n"

    def to_uf_quant_str(self) -> str:
        """Convert to UF quantifiied format
        """
        assert self.initialized
        z3_expr = self.to_chc_constraints()
        if self.has_bv:
            logic = "UFBV"
        elif self.has_int:
            logic = "UFLIA"
        elif self.has_real:
            logic = "UFLRA"
        else:
            logic = "ALL"
        return "(set-logic {})\n".format(logic) + z3_expr.sexpr() + "\n(check-sat)\n"

    def to_smt2(self) -> str:
        """Convert to SMT2 format"""
        return self.to_uf_quant_str()

    def to_z3_cnts(self) -> List:
        return self.all_variables, self.init, self.trans, self.post

    def simulate(self, steps=10, random_seed=None, concrete_init=None):
        """Simulate the execution of the transition system (similar to dynamic executions)

        FIXME: by LLM, to check.
        
        Args:
            steps: Number of simulation steps to perform
            random_seed: Optional seed for random choices
            concrete_init: Optional concrete initial state as a dictionary {var_name: value}
            
        Returns:
            List of states, where each state is a dictionary mapping variable names to values
        """
        assert self.initialized

        import random
        if random_seed is not None:
            random.seed(random_seed)

        # Create solver for checking conditions
        solver = z3.Solver()

        # Find an initial state
        state = {}
        if concrete_init:
            # Use provided initial state
            state = concrete_init.copy()
            # Verify that it satisfies the init condition
            state_constraints = []
            for var in self.variables:
                var_name = str(var)
                if var_name in state:
                    state_constraints.append(var == state[var_name])

            solver.push()
            solver.add(z3.And(state_constraints))
            solver.add(self.init)
            if solver.check() != z3.sat:
                raise ValueError("Provided initial state does not satisfy init condition")
            solver.pop()
        else:
            # Generate a random initial state
            solver.push()
            solver.add(self.init)
            if solver.check() != z3.sat:
                raise ValueError("Init condition is unsatisfiable")

            model = solver.model()
            for var in self.variables:
                var_name = str(var)
                value = model.eval(var, model_completion=True)
                state[var_name] = value
            solver.pop()

        # Store the sequence of states
        trace = [state.copy()]

        # Simulate steps
        for _ in range(steps):
            # Create constraints for current state
            current_state_constraints = []
            for var in self.variables:
                var_name = str(var)
                if var_name in state:
                    current_state_constraints.append(var == state[var_name])

            # Find next state
            solver.push()
            solver.add(z3.And(current_state_constraints))
            solver.add(self.trans)

            if solver.check() != z3.sat:
                # No valid next state
                break

            model = solver.model()
            next_state = {}

            # Extract values for next state
            for var in self.variables:
                var_name = str(var)
                # Find corresponding prime variable
                for prime_var in self.prime_variables:
                    prime_var_name = str(prime_var)
                    # Check if this is the prime version of var
                    if prime_var_name.endswith("!") and prime_var_name[:-1] == var_name:
                        value = model.eval(prime_var, model_completion=True)
                        next_state[var_name] = value
                        break
                    elif prime_var_name.endswith("'") and prime_var_name[:-1] == var_name:
                        value = model.eval(prime_var, model_completion=True)
                        next_state[var_name] = value
                        break
                    elif prime_var_name.endswith("_p") and prime_var_name[:-2] == var_name:
                        value = model.eval(prime_var, model_completion=True)
                        next_state[var_name] = value
                        break

            solver.pop()

            # Update current state
            state = next_state
            trace.append(state.copy())

            # Check if post-condition is violated
            solver.push()
            state_constraints = []
            for var in self.variables:
                var_name = str(var)
                if var_name in state:
                    state_constraints.append(var == state[var_name])

            solver.add(z3.And(state_constraints))
            solver.add(z3.Not(self.post))

            if solver.check() == z3.sat:
                print("Post-condition violated at step", len(trace) - 1)

            solver.pop()

        return trace
