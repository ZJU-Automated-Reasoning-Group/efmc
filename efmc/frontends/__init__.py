"""
Wrappers for the frontends
- Constraint Horn Clause (CHC)
- SyGuS invariant track
- VMT: TBD
- Btor2: TBD
"""

from .mini_sygus_parser import SyGusInVParser
from .chc_parser import CHCParser


def parse_chc(filename: str, to_real_type: bool):
    """Parse CHC file"""
    with open(filename, "r") as f:
        res = f.read()
        ss = CHCParser(res, to_real_type)
        return ss.get_transition_system()


def parse_sygus(filename: str, to_real_type: bool):
    """Parse SyGuS file"""
    with open(filename, "r") as f:
        res = f.read()
        ss = SyGusInVParser(res, to_real_type)
        return ss.get_transition_system()
