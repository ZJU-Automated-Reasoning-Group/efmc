"""
TBD: by LLM, to check.
"""

from z3 import *
from typing import List, Dict, Tuple, Optional, Any
import sys
import os

from efmc.engines.ef.templates.abstract_template import Template
from efmc.engines.ef.farkas.farkas import FarkasLemma
from efmc.sts import TransitionSystem
from efmc.utils.z3_expr_utils import big_and, big_or


class FarkasTemplate(Template):
    """
    Template-based invariant inference using Farkas' Lemma.
    
    This class implements template-based invariant inference for linear arithmetic
    using Farkas' Lemma to eliminate universal quantifiers, as described in:
    - "Constraint-Based Linear-Relations Analysis" (SAS'04)
    - "Non-Linear Loop Invariant Generation using Gröbner Bases" (POPL'04)
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        """
        Initialize the Farkas template.
        
        Args:
            sts: The transition system to analyze
            **kwargs: Additional arguments
        """
        self.sts = sts
        self.arity = len(self.sts.variables)

        # Number of template constraints (linear inequalities)
        self.num_templates = kwargs.get("num_templates", 3)

        # Template variables (coefficients for each variable in each template)
        self.template_vars = []
        self.template_index = 0

        # Initialize template variables
        self.add_template_vars()

        # Constraints for the template
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None

        # Initialize constraints
        self.add_template_cnts()

        # Farkas lemma instance for handling constraints
        self.farkas = FarkasLemma()

    def add_template_vars(self):
        """
        Initialize template variables.
        
        For each template constraint, we create coefficients for each variable
        and a constant term. For example, with variables x and y, we create:
        a*x + b*y + c >= 0
        where a, b, and c are template variables.
        """
        for _ in range(self.num_templates):
            self.template_index += 1
            # Create template variables for each constraint
            # First variable is the constant term
            tvars = [Real(f"p{self.template_index}_0")]
            # Create coefficients for each program variable
            for i in range(1, self.arity + 1):
                tvars.append(Real(f"p{self.template_index}_{i}"))
            self.template_vars.append(tvars)

    def add_template_cnts(self):
        """
        Add constraints for the template variables.
        
        This method creates constraints for:
        1. Initial states imply the invariant
        2. Invariant and transition relation imply the invariant in the next state
        3. Invariant implies the post-condition
        """
        # Constraints for initial states implying the invariant
        init_constraints = self._create_init_constraints()

        # Constraints for invariant and transition relation implying next-state invariant
        trans_constraints = self._create_trans_constraints()

        # Constraints for invariant implying post-condition
        post_constraints = self._create_post_constraints()

        # Combine constraints
        self.template_cnt_init_and_post = And(init_constraints, post_constraints)
        self.template_cnt_trans = trans_constraints

    def _create_init_constraints(self):
        """
        Create constraints for initial states implying the invariant.
        
        Returns:
            Z3 expression representing the constraints
        """
        # Apply Farkas' Lemma to eliminate universal quantifiers
        # We want to ensure: forall x. init(x) => inv(x)
        # This is equivalent to: not exists x. init(x) and not inv(x)

        # Create a new Farkas instance
        farkas = FarkasLemma()

        # Add initial state constraints
        farkas.add_constraint(self.sts.init)

        # Add negation of invariant template
        inv_expr = self._build_template_expr(self.template_vars, self.sts.variables)
        farkas.add_constraint(Not(inv_expr))

        # Apply Farkas' Lemma to get constraints on template variables
        farkas_constraints = farkas.apply_farkas_lemma(self.sts.variables)

        return And(farkas_constraints)

    def _create_trans_constraints(self):
        """
        Create constraints for invariant and transition relation implying next-state invariant.
        
        Returns:
            Z3 expression representing the constraints
        """
        # Apply Farkas' Lemma to eliminate universal quantifiers
        # We want to ensure: forall x,x'. inv(x) and trans(x,x') => inv(x')
        # This is equivalent to: not exists x,x'. inv(x) and trans(x,x') and not inv(x')

        # Create a new Farkas instance
        farkas = FarkasLemma()

        # Add current state invariant
        inv_expr = self._build_template_expr(self.template_vars, self.sts.variables)
        farkas.add_constraint(inv_expr)

        # Add transition relation
        farkas.add_constraint(self.sts.trans)

        # Add negation of next-state invariant
        next_inv_expr = self._build_template_expr(self.template_vars, self.sts.prime_variables)
        farkas.add_constraint(Not(next_inv_expr))

        # Apply Farkas' Lemma to get constraints on template variables
        all_vars = self.sts.variables + self.sts.prime_variables
        farkas_constraints = farkas.apply_farkas_lemma(all_vars)

        return And(farkas_constraints)

    def _create_post_constraints(self):
        """
        Create constraints for invariant implying post-condition.
        
        Returns:
            Z3 expression representing the constraints
        """
        # Apply Farkas' Lemma to eliminate universal quantifiers
        # We want to ensure: forall x. inv(x) => post(x)
        # This is equivalent to: not exists x. inv(x) and not post(x)

        # Create a new Farkas instance
        farkas = FarkasLemma()

        # Add invariant
        inv_expr = self._build_template_expr(self.template_vars, self.sts.variables)
        farkas.add_constraint(inv_expr)

        # Add negation of post-condition
        farkas.add_constraint(Not(self.sts.post))

        # Apply Farkas' Lemma to get constraints on template variables
        farkas_constraints = farkas.apply_farkas_lemma(self.sts.variables)

        return And(farkas_constraints)

    def _build_template_expr(self, template_vars, variables):
        """
        Build a template expression using the template variables and program variables.
        
        Args:
            template_vars: List of lists of template variables (coefficients)
            variables: List of program variables
            
        Returns:
            Z3 expression representing the template constraints
        """
        constraints = []

        for tvars in template_vars:
            # Build a linear expression: a*x + b*y + ... + c >= 0
            # where a, b, ... are template variables and x, y, ... are program variables
            expr = tvars[0]  # Constant term

            for i, var in enumerate(variables):
                if i < len(tvars) - 1:  # Ensure we don't go out of bounds
                    expr = expr + tvars[i + 1] * var

            constraints.append(expr >= 0)

        return And(constraints) if constraints else BoolVal(True)

    def build_invariant_expr(self, model, use_prime_variables=False):
        """
        Build an invariant expression from a model.
        
        Args:
            model: Z3 model containing values for template variables
            use_prime_variables: Whether to use prime variables in the invariant
            
        Returns:
            Z3 expression representing the invariant
        """
        variables = self.sts.prime_variables if use_prime_variables else self.sts.variables
        constraints = []

        for tvars in self.template_vars:
            # Build a linear expression: a*x + b*y + ... + c >= 0
            # where a, b, ... are template variables and x, y, ... are program variables
            expr = model.eval(tvars[0])  # Constant term

            for i, var in enumerate(variables):
                if i < len(tvars) - 1:  # Ensure we don't go out of bounds
                    coeff = model.eval(tvars[i + 1])
                    expr = expr + coeff * var

            constraints.append(expr >= 0)

        return And(constraints) if constraints else BoolVal(True)
