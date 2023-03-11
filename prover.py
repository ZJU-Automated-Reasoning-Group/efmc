""" Automated program verification for various transition systems specified in different formats

This file is the default external interface for calling different engines inside the `efmc` dir
"""

import logging
import os
import signal
import sys
import psutil
from efmc.sts import TransitionSystem
from efmc.frontends import parse_sygus, parse_chc
from efmc.engines.ef.ef_prover import EFProver
from efmc.engines.pdr.pdr_prover import PDRProver
from efmc.engines.kinduction.kinduction_prover import KInductionProver
from efmc.engines.qe import QuantifierEliminationProver
# from efmc.utils import is_entail

logger = logging.getLogger(__name__)

g_args = None  # the parsed arguments

# the invariant templates
g_int_real_templates = ["interval", "power_interval", "zone", "octagon", "poly"]
# "power_poly"
g_bv_templates = ["bv_interval", "power_bv_interval", "bv_zone", "power_bv_zone",
                  "bv_octagon", "power_bv_octagon",
                  "bv_affine", "bv_poly"]
# "power_bv_affine", "power_bv_poly"


def signal_handler(sig, frame):
    """The signal_handler function handles signals sent to the process.
    :param sig: Specify the signal that was caught
    :param frame: Get the stack frame of the signal
    :return: The signal number and the frame object
    """
    print("handling signals")
    parent = psutil.Process(os.getpid())
    for child in parent.children(recursive=True):
        child.kill()
    sys.exit(0)


def solve_with_qe(sts: TransitionSystem):
    """Use QE-based strongest inductive invariant inference"""
    qe_prover = QuantifierEliminationProver(sts)
    qe_prover.solve()


def solve_with_pdr(sts: TransitionSystem):
    """Use Z3's IC3/PDR engine (behind the CHC constraint language)"""
    chc_prover = PDRProver(sts)
    chc_prover.solve()


def solve_with_k_induction(sts: TransitionSystem):
    """Use K-induction"""
    print("K-induction starts..")
    kind_prover = KInductionProver(sts)
    if g_args.kind_aux_inv:
       kind_prover.use_aux_invariant = True
    kind_prover.solve(30)


def solve_with_ef(sts: TransitionSystem):
    """Use template-based invariant generation
    Currently, we solve the VC (exists-forall problems) via SMT
    """
    # Supported conjunctive domains: interval, zone, (bounded) polyhedrons, etc.
    ef_prover = EFProver(sts, prop_strengthen=g_args.prop_strengthen)  # use template and exists-forall solving
    # ef_prover.ignore_post_cond = True # an important flag
    if sts.has_bv:
        if g_args.template in g_bv_templates:
            # ef_prover.set_template("bv_interval")
            ef_prover.set_template(g_args.template)
            # the default one is "z3api"
            ef_prover.set_solver(g_args.smt_solver)
            # ef_prover.set_solver("cvc5")
        else:
            print("Unsupported template: ", g_args.template)
            print("You may try: ", g_bv_templates)
            exit(0)
    else:
        if g_args.template in g_int_real_templates:
            ef_prover.set_template(g_args.template)
            # ef_prover.set_template("power_interval")
            # ef_prover.set_template("interval")
        else:
            print("Unsupported template: ", g_args.template)
            print("You may try: ", g_int_real_templates)
            exit(0)

    ef_prover.solve()
    # ef_prover.solve_with_bin_solver()


def solve_chc_file(file_name: str, prover="efsmt"):
    """Solve a CHC file
    :param file_name: the CHC file
    :param prover: strategy
    """
    all_vars, init, trans, post = parse_chc(file_name, to_real_type=False)
    print("Finish parsing CHC file")
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])
    if sts.has_bv:
        # TODO: enforce to add this (or, infer automatically)
        sts.set_signedness("signed")

    # Currently, CHC is only used for bv?
    if prover == "efsmt":
        solve_with_ef(sts)
    elif prover == "pdr":
        """
        s = z3.SolverFor("HORN")
        s.add(z3.And(z3.parse_smt2_file(file_name)))
        res = s.check()
        print(res)
        """
        print("PDR starts working!")
        solve_with_pdr(sts)
    elif prover == "kind":
        solve_with_k_induction(sts)
    else:
        print("Not supported engine: {}".format(prover))
        exit(0)


def solve_sygus_file(filename: str, prover="all"):
    # FIXME: To use abstract domains and to preserve completeness,
    #   I cast integer variables to reals (this can be bad?) when parsing.
    #   A better idea is to transform the transition system after the parsing
    all_vars, init, trans, post = parse_sygus(filename, to_real_type=False)
    print("Finish parsing SyGuS file")
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])
    if sts.has_bv:
        # TODO: enforce to add this (or, infer automatically)
        #  e.g., check whether there are bvsle, bvslt, ... in the formula
        sts.set_signedness("unsigned")

    # print(sts)
    if prover == "efsmt":
        solve_with_ef(sts)
    elif prover == "pdr":
        # vars2, init2, trans2, post2 = parse_sygus(filename, to_real_type=False)
        solve_with_pdr(sts)
    elif prover == "kind":
        solve_with_k_induction(sts)
    else:
        solve_with_pdr(sts)


if __name__ == "__main__":
    import argparse

    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGQUIT, signal_handler)
    signal.signal(signal.SIGABRT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    # dir_path = os.path.dirname(os.path.realpath(__file__))
    # fib_04.sl needs disjunctive?
    # solve_sygus_file(dir_path + '/benchmarks/sygus-inv/LIA/2017.ASE_FiB/fib_01.sl', "efsmt")
    # solve_chc_file(dir_path + '/benchmarks/chc/bv/2017.ASE_FIB/32bits_signed/fib_15.sl_32bits_signed.smt2',
    #               prover="efsmt")
    #exit(0)
    parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--file', dest='file', default='none', type=str, help="Path to the input file")
    parser.add_argument('--engine', dest='engine', default='efsmt', type=str, help='''Set the engine:
  efsmt: template-based invariant generation + efsmt solving;
  pdr: property-directed reachability (we use the engine inside Z3);
  kind: k-induction''')
    parser.add_argument('--template', dest='template', default='interval', type=str,
                        help="The invariant template (only useful when the --engine=efsmt")
    parser.add_argument('--smt-solver', dest='smt_solver', default='z3api', type=str,
                        help="SMT solver (TODO: allow the user to specify a path to the solver?)")

    parser.add_argument('--prop-strengthen', dest='prop_strengthen', default=False, type=bool,
                        help="Enable property strengthening (currently, using 'T = T and Prop' as the template" )
    parser.add_argument('--kind-aux-inv', dest='kind_aux_inv', default=False, type=bool, help="Use aux invariant for k-induction (by default, k-induction does not need this)")
    parser.add_argument('--lang', dest='lang', default='sygus', type=str, help="The input format: sygus or chc")
    parser.add_argument('--timeout', dest='timeout', default=8, type=int, help="timeout")
    # parser.add_argument('--threads', dest='threads', default=4, type=int, help="threads")
    g_args = parser.parse_args()

    # python3 prover.py --file benchmarks/sygus-inv/LIA/2017.ASE_FiB/fib_01.sl --engine efsmt

    if g_args.lang == "sygus":
        solve_sygus_file(g_args.file, g_args.engine)
    elif g_args.lang == "chc":
        solve_chc_file(g_args.file, g_args.engine)
    else:
        print("Not supported format {}".format(g_args.lang))
        exit(0)
