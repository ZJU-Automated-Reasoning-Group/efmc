# coding: utf-8
from efmc.frontends.mini_sygus_parser import SyGusInVParser
from efmc.frontends.chc_parser import CHCParser

"""
Wrappers for the frontends
- CHC
- SyGuS invariant track
- VMT (verification modulo theory) 
- Btor2
"""


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
