"""
Convert SyGuS(invariant track) instances to C programs
"""
import os
import z3
from efmc.frontends import parse_sygus
from efmc.sts import TransitionSystem
from chc2c import compile_ira_to_c_sat

def process_pre(cnt):
    return cnt

def process_trans(cnt):
    return cnt

def process_post(cnt):
    return cnt


def parse_sygus_file(filename: str):
    # FIXME: To use abstract domains and to preserve completeness,
    #   I cast integer variables to reals (this can be bad?) when parsing.
    #   A better idea is to transform the transition system after the parsing
    all_vars, init, trans, post = parse_sygus(filename, to_real_type=True)
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])
    print(compile_ira_to_c_sat(init))
    print(compile_ira_to_c_sat(trans))
    print(compile_ira_to_c_sat(z3.simplify(post)))


if __name__ == "__main__":
    dir_path = os.path.dirname(os.path.realpath(__file__))
    parse_sygus_file(dir_path + "/benchmarks/sygus-inv/LIA/2017.ASE_FiB/fib_07.sl")
