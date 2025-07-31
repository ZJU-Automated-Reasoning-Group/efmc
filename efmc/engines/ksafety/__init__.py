"""
K-safety verification engine package.

This package provides verification of k-safety properties, which are properties
that relate multiple execution traces. Examples include:
- Non-interference (security)
- Determinism
- Symmetry properties
- Relational properties between different program versions
"""

from .base_prover import BaseKSafetyProver
from .non_interference import NonInterferenceProver
from .determinism import DeterminismProver

__all__ = [
    'BaseKSafetyProver',
    'NonInterferenceProver',
    'DeterminismProver'
]

