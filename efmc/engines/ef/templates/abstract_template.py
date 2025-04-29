"""
This module contains the abstract base class for template-based verification.

The Template class is an abstract base class that defines the interface for
template-based program verification. It provides methods for managing template
variables, constraints, and building invariants and ranking functions.

"""

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
    POLYNOMIAL = auto()

    # Disjunctive domains
    DISJUNCTIVE_INTERVAL = auto()
    DISJUNCTIVE_ZONE = auto()
    DISJUNCTIVE_OCTAGON = auto()
    DISJUNCTIVE_AFFINE = auto()
    DISJUNCTIVE_POLYHEDRON = auto()
    DISJUNCTIVE_POLYNOMIAL = auto()
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
    BV_KNOWNBITS = auto()
    BV_BITS_PREDICATE_ABSTRACTION = auto()
    BV_ENHANCED_PATTERN = auto()

    @classmethod
    def is_disjunctive(cls, template_type: 'TemplateType') -> bool:
        """Check if the template type is disjunctive."""
        return 'DISJUNCTIVE' in template_type.name

    @classmethod
    def is_bitvector(cls, template_type: 'TemplateType') -> bool:
        """Check if the template type uses bit-vector arithmetic."""
        return template_type.name.startswith('BV_')

    @classmethod
    def is_interval(cls, template_type: 'TemplateType') -> bool:
        """Check if the template type is an interval."""
        return template_type.name.startswith('INTERVAL')


class Template(ABC):
    """Abstract base class for template-based verification.
    
    This class defines the interface for template-based program verification,
    including methods for managing template variables, constraints, and
    building invariants and ranking functions.
    """

    @abstractmethod
    def add_template_vars(self) -> None:
        """Initialize the template variables.
        
        This method should set up all necessary template variables
        required for the verification process.
        """
        pass

    @abstractmethod
    def add_template_cnts(self) -> None:
        """Add constraints for the template variables.
        
        Adds constraints according to the specification of inductive loop invariant.
        These constraints define the shape and properties of the invariant.
        """
        pass

    @abstractmethod
    def build_invariant_expr(self, model: z3.ModelRef, use_prime_variables: bool) -> z3.ExprRef:
        """Build an invariant expression from a model.
        
        Args:
            model: Z3 model containing variable assignments
            use_prime_variables: If True, use primed variables (x', y'), otherwise use (x, y)
            
        Returns:
            Z3 expression representing the invariant
            If use_prime_variables is True, the expression should be in terms of the primed variables.
            Else, the expression should be in terms of the original variables.
        """
        pass
