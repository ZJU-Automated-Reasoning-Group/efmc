"""
Houdini templates for generating candidate invariants

This module provides template-based generation of candidate lemmas
for the Houdini invariant inference algorithm.
"""
import z3
from typing import List, Set
from itertools import combinations


class HoudiniTemplates:
    """Template generator for Houdini candidate lemmas"""
    
    def __init__(self, variables: List[z3.ExprRef]):
        self.variables = variables
        self.int_vars = [v for v in variables if v.sort() == z3.IntSort()]
        self.real_vars = [v for v in variables if v.sort() == z3.RealSort()]
        self.bv_vars = [v for v in variables if z3.is_bv_sort(v.sort())]
        self.bool_vars = [v for v in variables if v.sort() == z3.BoolSort()]

    def generate_all(self) -> List[z3.ExprRef]:
        """Generate all template-based candidate lemmas"""
        lemmas = []
        lemmas.extend(self.bounds_templates())
        lemmas.extend(self.ordering_templates())
        lemmas.extend(self.arithmetic_templates())
        lemmas.extend(self.equality_templates())
        lemmas.extend(self.sign_templates())
        return lemmas

    def bounds_templates(self) -> List[z3.ExprRef]:
        """Generate bound templates: x >= c, x <= c"""
        lemmas = []
        constants = [0, 1, -1, 2, -2, 10, -10]
        
        for var in self.int_vars + self.real_vars:
            for c in constants:
                lemmas.extend([var >= c, var <= c])
        
        # Bit-vector bounds
        for var in self.bv_vars:
            size = var.sort().size()
            max_val = (1 << (size - 1)) - 1
            min_val = -(1 << (size - 1))
            lemmas.extend([
                var >= 0,
                var <= max_val,
                var >= min_val
            ])
        
        return lemmas

    def ordering_templates(self) -> List[z3.ExprRef]:
        """Generate ordering templates: x <= y, x >= y"""
        lemmas = []
        
        for v1, v2 in combinations(self.int_vars + self.real_vars, 2):
            lemmas.extend([v1 <= v2, v1 >= v2])
        
        for v1, v2 in combinations(self.bv_vars, 2):
            if v1.sort() == v2.sort():
                lemmas.extend([v1 <= v2, v1 >= v2])
        
        return lemmas

    def arithmetic_templates(self) -> List[z3.ExprRef]:
        """Generate arithmetic relationship templates"""
        lemmas = []
        
        # Linear relationships: x + y >= 0, x - y >= 0
        for v1, v2 in combinations(self.int_vars + self.real_vars, 2):
            lemmas.extend([
                v1 + v2 >= 0,
                v1 - v2 >= 0,
                v1 + v2 <= 0,
                v1 - v2 <= 0
            ])
        
        # Multiplication by constants
        constants = [2, -1]
        for var in self.int_vars + self.real_vars:
            for c in constants:
                lemmas.extend([c * var >= 0, c * var <= 0])
        
        return lemmas

    def equality_templates(self) -> List[z3.ExprRef]:
        """Generate equality templates"""
        lemmas = []
        constants = [0, 1, -1]
        
        # Variable equals constant
        for var in self.int_vars + self.real_vars:
            for c in constants:
                lemmas.append(var == c)
        
        # Variable equality
        for v1, v2 in combinations(self.variables, 2):
            if v1.sort() == v2.sort():
                lemmas.append(v1 == v2)
        
        return lemmas

    def sign_templates(self) -> List[z3.ExprRef]:
        """Generate sign-based templates"""
        lemmas = []
        
        for var in self.int_vars + self.real_vars:
            lemmas.extend([
                var > 0,   # positive
                var < 0,   # negative
                var >= 0,  # non-negative
                var <= 0   # non-positive
            ])
        
        return lemmas

    def modular_templates(self) -> List[z3.ExprRef]:
        """Generate modular arithmetic templates"""
        lemmas = []
        moduli = [2, 3, 4]
        
        for var in self.int_vars:
            for m in moduli:
                for r in range(m):
                    lemmas.append(var % m == r)
        
        return lemmas

    def divisibility_templates(self) -> List[z3.ExprRef]:
        """Generate divisibility templates"""
        lemmas = []
        divisors = [2, 3, 4, 5]
        
        for var in self.int_vars:
            for d in divisors:
                lemmas.append(var % d == 0)
        
        return lemmas

    def boolean_templates(self) -> List[z3.ExprRef]:
        """Generate boolean templates"""
        lemmas = []
        
        # Simple boolean values
        for var in self.bool_vars:
            lemmas.extend([var, z3.Not(var)])
        
        # Boolean combinations
        for v1, v2 in combinations(self.bool_vars, 2):
            lemmas.extend([
                z3.And(v1, v2),
                z3.Or(v1, v2),
                z3.Implies(v1, v2)
            ])
        
        return lemmas


def generate_templates(variables: List[z3.ExprRef], 
                      template_types: Set[str] = None) -> List[z3.ExprRef]:
    """
    Convenient function to generate templates
    
    Args:
        variables: List of program variables
        template_types: Set of template types to generate
                       Options: 'bounds', 'ordering', 'arithmetic', 'equality', 'sign'
                       If None, generates all types
    """
    if template_types is None:
        template_types = {'bounds', 'ordering', 'arithmetic', 'equality', 'sign'}
    
    generator = HoudiniTemplates(variables)
    lemmas = []
    
    if 'bounds' in template_types:
        lemmas.extend(generator.bounds_templates())
    if 'ordering' in template_types:
        lemmas.extend(generator.ordering_templates())
    if 'arithmetic' in template_types:
        lemmas.extend(generator.arithmetic_templates())
    if 'equality' in template_types:
        lemmas.extend(generator.equality_templates())
    if 'sign' in template_types:
        lemmas.extend(generator.sign_templates())
    if 'modular' in template_types:
        lemmas.extend(generator.modular_templates())
    if 'divisibility' in template_types:
        lemmas.extend(generator.divisibility_templates())
    if 'boolean' in template_types:
        lemmas.extend(generator.boolean_templates())
    
    return lemmas


# Demo usage
if __name__ == "__main__":
    # Example with integer variables
    x, y, z = z3.Ints("x y z")
    variables = [x, y, z]
    
    templates = generate_templates(variables, {'bounds', 'ordering'})
    print(f"Generated {len(templates)} templates for variables {variables}")
    
    # Show first few templates
    for i, template in enumerate(templates[:10]):
        print(f"  {i+1}: {template}")
