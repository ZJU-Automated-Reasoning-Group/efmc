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
        allowed_keys = {'variables', 'prime_variables', 'init', 'trans', 'post'}
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
        else:
            raise NotImplementedError

        self.initialized = True
        # self.analyze_and_simplify() # is this OK?

    def analyze_and_simplify(self):
        """Simplify the problem?"""
        self.trans = ctx_simplify(self.trans)  # ctx_simplify can be slow

    def to_chc_constraints(self) -> z3.ExprRef:
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
        """Convert to CHC format"""
        sol = z3.Solver()
        sol.add(self.to_chc_constraints())
        return "(set-logic HORN)\n" + sol.to_smt2()
