"""
FIXME: this file is not used yet

For examples, 
1. the parity domain 
$\psi(a) := (a \mod 2 = 0)$ that 
checks for a program variable of bit vector type, whether even or odd, if interpreted as an unsigned integer. A true abstract value thus represents a variable with always even values, whereas a false value represents a variable that only contains odd values during any computation.

2.  The bit masks domain $\mathcal{BM}_\perp = (\{0, \ldots, \texttt{bw}-1\} \to \{0, 1, *\}) \cup \{\perp\}$ captures must-information about the individual bits of a variable's possible values during execution. 
Here, the domain consists of functions mapping bit positions in a bit vector to one of three possible values: \(0\) (definitely zero), \(1\) (definitely one), or \(*\) (unknown).
The $\top$ element of this domain is the function $(\lambda x \mathbin{.} *)$ that represents no information about any position of the bit vector.
"""

from efmc.engines.ef.templates.abstract_template import TemplateType, Template
from efmc.sts import TransitionSystem
from efmc.utils import get_variables

class ParityTemplate(Template):
    # refer to class BitVecIntervalTemplate in this repository and description above
    def __init__(self, ts: TransitionSystem):
        super().__init__(ts)
        self.template_type = TemplateType.PARITY
    
    def add_template_vars(self):
        self.template_vars = get_variables(self.sts.variables)

    def get_additional_cnts_for_template_vars(self):
        return z3.BoolVal(True)
    
    def add_template_cnts(self):
        cnts = []
        return cnts
    

class BitMasksTemplate(Template):
    def __init__(self, ts: TransitionSystem):
        super().__init__(ts)
        self.template_type = TemplateType.BITMASKS
        
    def add_template_vars(self):
        self.template_vars = get_variables(self.sts.variables)

    def get_additional_cnts_for_template_vars(self):
        return z3.BoolVal(True)
    
    def add_template_cnts(self):
        cnts = []
        return cnt
