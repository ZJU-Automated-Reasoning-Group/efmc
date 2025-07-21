"""
Template-based invariant inference using Farkas' Lemma.
"""
from z3 import *
from typing import List

from efmc.engines.ef.templates.abstract_template import Template
from efmc.engines.ef.farkas.farkas_lemma import FarkasLemma
from efmc.sts import TransitionSystem


class FarkasTemplate(Template):
    """
    Template-based invariant inference using Farkas' Lemma for linear arithmetic.
    
    Creates linear templates of the form: a₁x₁ + a₂x₂ + ... + c ≥ 0
    Uses Farkas' Lemma to eliminate universal quantifiers from verification conditions.
    """

    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        self.arity = len(self.sts.variables)
        self.num_templates = kwargs.get("num_templates", 3)
        
        self.template_vars = []
        self.template_index = 0
        self.template_cnt_init_and_post = None
        self.template_cnt_trans = None
        
        self.add_template_vars()
        self.add_template_cnts()

    def add_template_vars(self):
        """Initialize template variables for linear expressions."""
        for _ in range(self.num_templates):
            self.template_index += 1
            # Create coefficients: [constant, coeff_x1, coeff_x2, ...]
            tvars = [Real(f"p{self.template_index}_{i}") for i in range(self.arity + 1)]
            self.template_vars.append(tvars)

    def add_template_cnts(self):
        """Generate constraints using Farkas' Lemma."""
        init_constraints = self._create_farkas_constraints(
            self.sts.init, z3.Not(self._build_template_expr(self.sts.variables))
        )
        
        trans_constraints = self._create_farkas_constraints(
            z3.And(self._build_template_expr(self.sts.variables), self.sts.trans),
            z3.Not(self._build_template_expr(self.sts.prime_variables))
        )
        
        post_constraints = self._create_farkas_constraints(
            self._build_template_expr(self.sts.variables), z3.Not(self.sts.post)
        )
        
        self.template_cnt_init_and_post = z3.And(init_constraints, post_constraints)
        self.template_cnt_trans = trans_constraints

    def _create_farkas_constraints(self, premise, conclusion):
        """Create Farkas constraints for premise → conclusion."""
        farkas = FarkasLemma()
        farkas.add_constraint(premise)
        farkas.add_constraint(conclusion)
        
        # Get all variables involved
        all_vars = list(set(self.sts.variables + self.sts.prime_variables))
        constraints = farkas.apply_farkas_lemma(all_vars)
        return z3.And(constraints) if constraints else z3.BoolVal(True)

    def _build_template_expr(self, variables):
        """Build template expression: ∧ᵢ(aᵢ₁x₁ + aᵢ₂x₂ + ... + cᵢ ≥ 0)."""
        constraints = []
        for tvars in self.template_vars:
            # Linear expression: constant + sum(coeff * var)
            expr = tvars[0]  # constant term
            for i, var in enumerate(variables):
                if i + 1 < len(tvars):
                    expr = expr + tvars[i + 1] * var
            constraints.append(expr >= 0)
        return z3.And(constraints) if constraints else z3.BoolVal(True)

    def build_invariant_expr(self, model, use_prime_variables=False):
        """Build invariant from model values."""
        variables = self.sts.prime_variables if use_prime_variables else self.sts.variables
        constraints = []
        
        for tvars in self.template_vars:
            # Evaluate template variables from model
            expr = model.eval(tvars[0])  # constant
            for i, var in enumerate(variables):
                if i + 1 < len(tvars):
                    coeff = model.eval(tvars[i + 1])
                    expr = expr + coeff * var
            constraints.append(expr >= 0)
        
        return z3.And(constraints) if constraints else z3.BoolVal(True)

