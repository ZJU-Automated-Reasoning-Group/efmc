from enum import Enum, auto
from typing import Optional
from abc import ABC, abstractmethod
import z3


class TemplateType(Enum):
    """Enumeration of supported template types for program verification.
    
    Categories:
    - Basic: Simple numeric domains (INTERVAL, ZONE, etc.)
    - Disjunctive: Unions of basic domains
    - Bit-Vector: Templates for bit-vector arithmetic
    - Special: Arrays, strings, floating-point
    """
    # Basic numeric domains
    INTERVAL = auto()
    ZONE = auto()
    OCTAGON = auto()
    AFFINE = auto()
    POLYHEDRON = auto()
    
    # Disjunctive domains
    DISJUNCTIVE_INTERVAL = auto()
    DISJUNCTIVE_ZONE = auto()
    DISJUNCTIVE_OCTAGON = auto()
    DISJUNCTIVE_AFFINE = auto()
    DISJUNCTIVE_POLYHEDRON = auto()
    
    # Special domains
    ARRAY = auto()
    STRING = auto()
    FLOAT = auto()
    
    # Bit-vector domains
    BV_INTERVAL = auto()
    BV_ZONE = auto()
    BV_OCTAGON = auto()
    BV_AFFINE = auto()
    BV_POLYHEDRON = auto()
    BV_DISJUNCTIVE_INTERVAL = auto()
    BV_DISJUNCTIVE_ZONE = auto()
    BV_DISJUNCTIVE_OCTAGON = auto()
    BV_DISJUNCTIVE_AFFINE = auto()
    BV_DISJUNCTIVE_POLYHEDRON = auto()
    BV_BITMASK = auto()


    @classmethod
    def is_disjunctive(cls, template_type: 'TemplateType') -> bool:
        """Check if the template type is disjunctive."""
        return 'DISJUNCTIVE' in template_type.name
    
    @classmethod
    def is_bitvector(cls, template_type: 'TemplateType') -> bool:
        """Check if the template type uses bit-vector arithmetic."""
        return template_type.name.startswith('BV_')   


class Template(object):
    """Abstract interface for template-based verification
    """

    def add_template_vars(self):
        """Initialize the template variables"""
        pass

    def add_template_cnts(self):
        """Add constraints for the template variables (according to specification of inductive loop invariant)
        TODO: in some cases, we may want to iteratively/gradually add new constraints
         to the template variables. Perhaps we need to  design a good interface for doing this.
         (For example, we may want to compute the "minimal/most precise" inductive invariant).
        """
        pass

    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables: bool):
        """Build an invariant from a model, i.e., finding assignments of the template vars
        :param model the model used for building expr
        :param use_prime_variables deciding using x, y or x!, y!
        """
        pass

    def add_template_cnts_for_ranking_function(self):
        """Add constraints for the template variables (according to specification of ranking function)
        """
        pass

    def build_ranking_function_expr(self):
        """Building the expression for the ranking function"""
        pass
