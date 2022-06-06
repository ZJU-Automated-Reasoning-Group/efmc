# coding: utf-8
from z3 import *

"""
TODO: https://github.com/dynaroars/program_analysis_notes/blob/6af266996423d8add16dbb4cd5e4f998778659c4/code/iconstructs.py
The above one uses Sage, which is heavyweight
"""


class Farkas(object):

    def myconvert(self):
        """
        e < 0  =>  e     < 0,
        e > 0  => -e     < 0,
        e <= 0 =>  e - 1 < 0, because e <= 0 == e < 1  ==  e - 1 < 0
        e >= 0 => -e - 1 < 0, because e >= 0 == e > -1 ==  e + 1 > 0 ==  -e-1 <0
        e == 0 =>  ????

        """
        return

    def farkas(self, uvs, eid=None):
        """
        uvs:  universal quantified variables, e.g., [x,y]

        The formula -50*a1 + a2*y + a3 >= 0 has four variables
             ['y, a1, a2, a3']

        1. The result of  (-50*a1 + a2*y + a3 >= 0).farkas([x,y]) should be
        (50*a1*ld - a3*ld + LD - ld == 0 and -a2*ld == 0 and ld >= 0 and LD > 0)

        2. The result of (-50*a1+a2*y+a3*x >= 0).farkas([x,y]) should be
        (50*a1*ld + LD - ld == 0 and -a3*ld == 0 and -a2*ld == 0 and ld >= 0 and LD > 0)
        """

        raise NotImplementedError

    def farkas_conjunction(self, uvs):
        """
        sage: var('y, a1, a2, a3, a4, a5, a6')
        (y, a1, a2, a3, a4, a5, a6)

        print FAnd(FOr(FBool(False),-50*a1+a2*y+a3 >= 0, \
        -50*a4+a5*y+a6 >= 0),-80*a3+a1+8*a2*y>=0).farkas([x,y])

        50*a1*ld_0_0 - a3*ld_0_0 + 50*a4*ld_0_1 -
        a6*ld_0_1 + LD0 - ld_0_0 - ld_0_1 == 0
        and -a2*ld_0_0 - a5*ld_0_1 == 0 and ld_0_0 >= 0
        and ld_0_1 >= 0
        and LD0 > 0
        and -a1*ld1 + 80*a3*ld1 + LD1 - ld1 == 0
        and
        -8*a2*ld1 == 0
        and ld1 >= 0
        and LD1 > 0)
        """
        raise NotImplementedError
