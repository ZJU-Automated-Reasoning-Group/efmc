# coding: utf-8
# import time
# from z3 import *
from typing import List
from .utils import ctx_simplify


class TransitionSystem(object):
    """
    TODO: This is a trivial transition system with several restrictions
       1. Only one invariant
       2. Number of self.variables and self.prime_variables are the same
       3. All variables in self.variables have the same type, e.g., real/int
      We should break 3 to support arrays
    """

    def __init__(self):
        self.all_variables = []  # self.variables + self.prime_variables
        self.variables = []  # x, y
        self.prime_variables = []  # x!, y!
        self.trans = None  # formula about the relation of x, y, x!, y!
        self.init = None  # formula about x, y
        self.post = None  # formula about x, y
        self.initialized = False

        self.has_bv = False
        self.has_array = False

    def __repr__(self):
        print(self.all_variables)
        print(self.init)
        print(self.trans)
        print(self.post)
        return " "

    def from_z3_cnts(self, ts: List):
        """
        A trick for initializing sts
        """
        self.all_variables, self.init, self.trans, self.post = ts[0], ts[1], ts[2], ts[3]
        # print(self.all_variables)
        for var in self.all_variables:
            # print(str(var))
            # FIXME: using name is not a good and general idea
            if str(var).endswith('!'):
                self.prime_variables.append(var)
            else:
                self.variables.append(var)
        # print(self.variables, self.prime_variables)
        self.initialized = True
        # self.analyze_and_simplify() # is this OK?
        # exit(0)

    def analyze_and_simplify(self):
        """
        Simplify the problem?
        """
        self.trans = ctx_simplify(self.trans)
