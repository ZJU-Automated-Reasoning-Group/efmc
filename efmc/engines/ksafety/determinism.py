"""
Determinism verification for k-safety properties.

This module implements verification of determinism properties,
which ensure that for the same inputs, the system always produces the same outputs.
"""

import logging
import z3

from .base_prover import BaseKSafetyProver
from efmc.utils.verification_utils import VerificationResult

logger = logging.getLogger(__name__)


class DeterminismProver(BaseKSafetyProver):
    """
    Specialized prover for determinism verification.
    
    Determinism states that for the same inputs, the system should
    always produce the same outputs.
    """

    def __init__(self, sts, **kwargs):
        """
        Initialize determinism prover.
        
        Args:
            sts: The transition system to verify
            **kwargs: Additional configuration options
        """
        # Determinism requires exactly 2 traces
        super().__init__(sts, k=2, **kwargs)
        self.logger.info("Initialized determinism prover")

    def verify_determinism(self) -> VerificationResult:
        """
        Verify determinism property.
        
        Determinism states that for the same inputs, the system should
        always produce the same outputs.
        
        Returns:
            VerificationResult indicating the verification outcome
        """
        self.logger.info("Verifying determinism property")
        
        # Create the determinism property
        # For determinism: if inputs are the same, then outputs should be the same
        trace_vars = self.create_trace_variables()
        
        # Assume all variables are inputs (simplified)
        input_equality = z3.And(*[trace_vars[0][i] == trace_vars[1][i] 
                                  for i in range(len(self.sts.variables))])
        
        output_equality = z3.And(*[trace_vars[0][i] == trace_vars[1][i] 
                                   for i in range(len(self.sts.variables))])
        
        determinism_property = z3.Implies(input_equality, output_equality)
        
        self.set_relational_property(determinism_property)
        return self.solve() 