# coding: utf-8
# import time
import psutil
import signal
import logging
from efmc.ef_prover import EFProver
from efmc.frontend import parse_sygus, parse_chc
from efmc.pdr_prover import PDRProver
from efmc.qe_prover import QuantifierEliminationProver
from efmc.sts import TransitionSystem
from efmc.symabs_prover import SymbolicAbstractionProver
from z3 import *
from efmc.utils import is_entail


logger = logging.getLogger(__name__)


"""
Automated verification
"""


def signal_handler(sig, frame):
    """
    Captures the shutdown signals and cleans up all child processes of this process.
    """
    parent = psutil.Process(os.getpid())
    for child in parent.children(recursive=True):
        child.kill()
    sys.exit(0)


def solve_with_qe(sts: TransitionSystem):
    """
    Use QE-based strongest inductive invariant inference
    """
    qe_prover = QuantifierEliminationProver(sts)
    qe_prover.solve()


def solve_with_chc(sts: TransitionSystem):
    """
    Use Z3's IC3/PDR engine (behind the CHC constraint language)
    """
    chc_prover = PDRProver(sts)
    chc_prover.solve()


def solve_with_ef(sts: TransitionSystem):
    """
    Use template-based invariant generation
    Currently, we solve the VC (exists-forall problems) via SMT
    """
    # Supported conjunctive domains: interval, zone, (bounded) polyhedrons, etc.
    ef_prover = EFProver(sts)  # use template and exists-forall solving
    if sts.has_bv:
        ef_prover.set_template("bv_interval")
    else:
        ef_prover.set_template("poly")
        # ef_prover.set_template("power_interval")
        # ef_prover.set_template("interval")
    ef_prover.solve()


def solve_with_symabs(sts: TransitionSystem):
    """
    Use symbolic abstraction based abstract interpretation
    """
    symabs_prover = SymbolicAbstractionProver(sts)
    symabs_prover.solve()


def check_invariant(sts: TransitionSystem, inv: z3.ExprRef, inv_in_prime_variables: z3.ExprRef):
    """
    For quick testing
    """
    correct = True
    if not is_entail(sts.init, inv):
        correct = False
        print("Init wrong!")
    if not is_entail(z3.And(sts.trans, inv), inv_in_prime_variables):
        correct = False
        print("Inductive wrong!")
    if not is_entail(inv, sts.post):
        correct = False
        print("Post wrong!")
    if not correct:
        print("Invariant not success!")
        print(sts)
        print("Inv: ", inv)
    else:
        print("Invariant check success!")


def validate_invariant(sts: TransitionSystem):
    # for quick testing
    x, n, px, pn = Reals("x n x! n!")
    inv = Or(And(1 <= x, 1 >= x, 1 <= n, 1 >= n),
             And(Not(n <= 0), x == 0))
    inv_in_prime = Or(And(1 <= px, 1 >= px, 1 <= pn, 1 >= pn),
                      And(Not(pn <= 0), px == 0))
    check_invariant(sts, inv, inv_in_prime)


def solve_chc_file(filename: str, prover="efsmt"):
    # Currently, CHC is only used for bv
    all_vars, init, trans, post = parse_chc(filename, to_real_type=False)
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])
    sts.has_bv = True
    solve_with_ef(sts)
    # s = SolverFor("HORN")
    # s.add(z3.And(parse_smt2_file(filename)))
    # print(s.check())


def solve_sygus_file(filename: str, prover="all"):
    """
    Currently, we support the sygus frontend
    """
    # FIXME: To use abstract domains and to preserve completeness,
    # FIXME: I cast integer variables to reals (this can be bad?) when parsing.
    # FIXME: A better idea is to transform the transition system after the parsing
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
    elif prover == "test":
        validate_invariant(sts)
    else:
        solve_with_ef(sts)
        solve_with_chc(sts)
        solve_with_symabs(sts)


if __name__ == "__main__":
    import argparse

    # solve_chc_file("./benchmarks/bv/simple.smt2", "efsmt")
    solve_chc_file("/Users/prism/Work/eldarica-bin/tests/sygus/fib_44.sl.smt2", "efsmt")

    # solve_sygus_file("./benchmarks/sygus-inv/LIA/2017.ASE_FiB/minor1.sl", "symabs")
    # solve_sygus_file("./benchmarks/sygus-inv/LIA/2017.ASE_FiB/minor1.sl", "efsmt")
    # fib_04.sl needs disjunctive?
    # solve_sygus_file("/Users/prism/Work/logicbox/independent/efsmt/benchmarks/sygus-inv/LIA/2017.ASE_FiB/fib_01.sl", "efsmt")
    # solve_sygus_file("/Users/prism/Work/logicbox/independent/efsmt/benchmarks/sygus-inv/LIA/2018.NeurIPS_Code2Inv/38.c.sl", "efsmt")
    # solve_sygus_file("./benchmarks/sygus-inv/LIA/2017.ASE_FiB/vardep.sl")
    # solve_sygus_file("/Users/prism/Work/logicbox/independent/efsmt/benchmarks/sygus-inv/LIA/2017.ASE_FiB/fib_35.sl", "symabs")
    # solve_sygus_file("/Users/prism/Work/logicbox/independent/efsmt/benchmarks/sygus-inv/LIA/2017.ASE_FiB/fib_35.sl", "efsmt")
    exit(0)
    parser = argparse.ArgumentParser()
    parser.add_argument('--file', dest='file', default='none', type=str, help="file")
    parser.add_argument('--prover', dest='prover', default='efsmt', type=str, help="The prover for using")
    # parser.add_argument('--timeout', dest='timeout', default=8, type=int, help="timeout")
    # parser.add_argument('--threads', dest='threads', default=4, type=int, help="threads")
    args = parser.parse_args()

    # Registers signal handler so we can kill all of our child processes.
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGQUIT, signal_handler)
    signal.signal(signal.SIGABRT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    solve_sygus_file(args.file, args.prover)
