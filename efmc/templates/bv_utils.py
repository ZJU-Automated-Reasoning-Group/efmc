"""
Facilities for bit-vector related staff
"""
from enum import Enum


class Signedness(Enum):
    SIGNED = 0
    UNSIGNED = 1
    UNKNOWN = 2
