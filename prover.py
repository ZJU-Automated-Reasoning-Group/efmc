""" Automated program verification for various transition systems specified in different formats

This file is the default external interface for calling different engines inside the `efmc` dir
"""

import logging
import os
import signal
import sys
import psutil
import z3
from efmc.engines.ef.ef_prover import EFProver
from efmc.frontends import parse_sygus, parse_chc
from efmc.engines.pdr.pdr_prover import PDRProver
from efmc.engines.qe import QuantifierEliminationProver
from efmc.sts import TransitionSystem
from efmc.engines.symabs import SymbolicAbstractionProver
# from efmc.utils import is_entail

logger = logging.getLogger(__name__)


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


def solve_with_chc(sts: TransitionSystem):
    """Use Z3's IC3/PDR engine (behind the CHC constraint language)"""
    chc_prover = PDRProver(sts)
    chc_prover.solve()


def solve_with_ef(sts: TransitionSystem):
    """Use template-based invariant generation
    Currently, we solve the VC (exists-forall problems) via SMT
    """
    # Supported conjunctive domains: interval, zone, (bounded) polyhedrons, etc.
    ef_prover = EFProver(sts)  # use template and exists-forall solving
    if sts.has_bv:
        # ef_prover.ignore_post_cond = True # an important flag
        ef_prover.set_template("bv_interval")
    else:
        ef_prover.set_template("poly")
        # ef_prover.set_template("power_interval")
        # ef_prover.set_template("interval")
    ef_prover.solve()
    # ef_prover.solve_with_bin_solver()


def solve_with_symabs(sts: TransitionSystem):
    """Use symbolic abstraction based abstract interpretation"""
    symabs_prover = SymbolicAbstractionProver(sts)
    symabs_prover.solve()


def solve_chc_file(file_name: str, prover="efsmt"):
    """Solve a CHC file
    :param file_name: the CHC file
    :param prover: strategy
    """
    # Currently, CHC is only used for bv?
    if prover == "efsmt":
        all_vars, init, trans, post = parse_chc(file_name, to_real_type=False)
        logger.debug("Finish parsing")
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        solve_with_ef(sts)
    elif prover == "pdr":
        s = z3.SolverFor("HORN")
        s.add(z3.And(z3.parse_smt2_file(file_name)))
        print("PDR starts working!")
        res = s.check()
        print(res)
    else:
        print("Not supported engine: {}".format(prover))
        exit(0)


def solve_sygus_file(filename: str, prover="all"):
    # FIXME: To use abstract domains and to preserve completeness,
    #   I cast integer variables to reals (this can be bad?) when parsing.
    #   A better idea is to transform the transition system after the parsing
    all_vars, init, trans, post = parse_sygus(filename, to_real_type=True)
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])
    # print(sts)
    if prover == "efsmt":
        solve_with_ef(sts)
    elif prover == "pdr":
        # vars2, init2, trans2, post2 = parse_sygus(filename, to_real_type=False)
        solve_with_chc(sts)
    elif prover == "qe":
        solve_with_qe(sts)
    elif prover == "symabs":
        solve_with_symabs(sts)
    else:
        solve_with_ef(sts)
        solve_with_chc(sts)
        solve_with_symabs(sts)


if __name__ == "__main__":
    import argparse

    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGQUIT, signal_handler)
    signal.signal(signal.SIGABRT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    dir_path = os.path.dirname(os.path.realpath(__file__))
    # fib_04.sl needs disjunctive?
    solve_sygus_file(dir_path + '/benchmarks/sygus-inv/LIA/2017.ASE_FiB/fib_01.sl', "efsmt")
    exit(0)
    parser = argparse.ArgumentParser()
    parser.add_argument('--file', dest='file', default='none', type=str, help="Path to the input file")
    parser.add_argument('--prover', dest='prover', default='efsmt', type=str, help="The prover for using")
    parser.add_argument('--format', dest='format', default='sygus', type=str, help="The input format")
    # parser.add_argument('--timeout', dest='timeout', default=8, type=int, help="timeout")
    # parser.add_argument('--threads', dest='threads', default=4, type=int, help="threads")
    args = parser.parse_args()

    if args.format == "sygus":
        solve_sygus_file(args.file, args.prover)
    elif args.format == "chc":
        solve_chc_file(args.file, args.prover)
    else:
        print("Not supported format {}".format(args.foramt))
        exit(0)
