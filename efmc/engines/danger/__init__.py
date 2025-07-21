"""
Danger Invariant Engine

This module implements danger invariant synthesis for safety verification.
Danger invariants provide a dual approach to traditional safety invariants
by proving that all reachable states will eventually lead to safe states.
"""

from .danger_inv import DangerInvariantProver

__all__ = ['DangerInvariantProver'] 