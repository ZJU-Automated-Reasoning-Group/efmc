""" Automated program verification for various transition systems specified in different formats
This file is the default external interface for calling different engines inside the `efmc` dir
"""

import logging
import os
import signal
import subprocess
import sys
from threading import Timer
from typing import List

import psutil

from efmc.engines.ef.ef_prover import EFProver
from efmc.engines.kinduction.kind_prover import KInductionProver
from efmc.engines.pdr.pdr_prover import PDRProver
from efmc.engines.qe import QuantifierEliminationProver
from efmc.frontends import parse_sygus, parse_chc
from efmc.sts import TransitionSystem
from efmc.utils.global_config import g_verifier_args  # the parsed arguments

logger = logging.getLogger(__name__)

# the invariant templates
g_int_real_templates = ["interval", "power_interval",
                        "zone", "octagon",
                        "affine", "power_affine",
                        "poly", "power_poly"]
# "power_poly"
g_bv_templates = ["bv_interval", "power_bv_interval",
                  "bv_zone", "power_bv_zone",
                  "bv_octagon", "power_bv_octagon",
                  "bv_poly", "power_bv_poly"]


# "bv_affine", "power_bv_affine"

def setup_signal_handlers():
    """Configure signal handlers for graceful termination."""

    def handler(sig, frame):
        logger.info("Handling termination signal")
        parent = psutil.Process(os.getpid())
        for child in parent.children(recursive=True):
            child.kill()
        sys.exit(0)

    for sig in [signal.SIGINT, signal.SIGQUIT, signal.SIGABRT, signal.SIGTERM]:
        signal.signal(sig, handler)


def terminate(process: subprocess.Popen, is_timeout: List[bool]):
    if process.poll() is None:
        try:
            # process.terminate()
            os.kill(process.pid, signal.SIGKILL)
            is_timeout[0] = True
        except Exception as es:
            # print("error for interrupting")
            print(es)
            pass


def solve_with_bin_solver(cmd: List[str], timeout=3600) -> str:
    """ cmd should be a complete cmd"""
    is_timeout = [False]

    p = subprocess.Popen(cmd, stderr=subprocess.STDOUT)
    timer = Timer(timeout, terminate, args=[p, is_timeout])
    timer.start()
    p.wait()
    timer.cancel()


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
    global g_verifier_args
    print("K-induction starts..")
    kind_prover = KInductionProver(sts)
    if g_verifier_args.kind_aux_inv:
        kind_prover.use_aux_invariant = True
    kind_prover.solve(int(g_verifier_args.kind_k))


def solve_with_ef(sts: TransitionSystem):
    """Use template-based invariant generation
    Currently, we solve the VC (exists-forall problems) via SMT
    """
    # ef_prover.ignore_post_cond = True # an important flag
    global g_verifier_args
    if sts.has_bv:
        if "bv" not in g_verifier_args.template:
            print("Unsupported template: ", g_verifier_args.template)
            print("You may try: ", g_bv_templates)
            exit(0)
            
        if g_verifier_args.prevent_over_under_flows > 0:
            ef_prover = EFProver(sts, prop_strengthen=g_verifier_args.prop_strengthen,
                                 validate_invariant=g_verifier_args.validate_invariant,
                                 no_overflow=True, no_underflow=True, pysmt_solver=g_verifier_args.pysmt_solver)
        else:
            ef_prover = EFProver(sts, prop_strengthen=g_verifier_args.prop_strengthen,
                                 validate_invariant=g_verifier_args.validate_invariant,
                                 no_overflow=False, no_underflow=False, pysmt_solver=g_verifier_args.pysmt_solver)
        if g_verifier_args.template in g_bv_templates:
            # ef_prover.set_template("bv_interval")
            ef_prover.set_template(g_verifier_args.template, num_disjunctions=g_verifier_args.num_disjunctions)
            # the default one is "z3api"
            ef_prover.set_solver(g_verifier_args.efsmt_solver)
            # ef_prover.set_solver("cvc5")
        else:
            print("Unsupported template: ", g_verifier_args.template)
            print("You may try: ", g_bv_templates)
            exit(0)
    else:
        ef_prover = EFProver(sts, prop_strengthen=g_verifier_args.prop_strengthen,
                             validate_invariant=g_verifier_args.validate_invariant,
                             pysmt_solver=g_verifier_args.pysmt_solver)
        if g_verifier_args.template in g_int_real_templates:
            ef_prover.set_template(g_verifier_args.template, num_disjunctions=g_verifier_args.num_disjunctions)
            # the default one is "z3api"
            ef_prover.set_solver(g_verifier_args.efsmt_solver)
            # ef_prover.set_solver("cvc5")
            # ef_prover.set_template("power_interval")   ("interval")
        else:
            print("Unsupported template: ", g_verifier_args.template)
            print("You may try: ", g_int_real_templates)
            exit(0)

    if g_verifier_args.dump_ef_smt2 or g_verifier_args.dump_qbf:
        ef_prover.dump_constraint(g_verifier_args)
    else:
        res = ef_prover.solve()
        if res == "sat":
            print("safe")
        else:
            print("unknown")


def solve_chc_file(file_name: str, prover="efsmt"):
    """Solve a CHC file
    :param file_name: the CHC file
    :param prover: strategy
    """
    # global g_verifier_args
    if prover == "eld":
        cmd = ["./bin_solvers/bin/eld", file_name]
        solve_with_bin_solver(cmd, g_verifier_args.timeout)
        return

    all_vars, init, trans, post = parse_chc(file_name, to_real_type=False)
    print("Finish parsing CHC file")
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])
    if sts.has_bv:
        if g_verifier_args.signedness == "signed":
            sts.set_signedness("signed")
        elif g_verifier_args.signedness == "unsigned":
            sts.set_signedness("unsigned")
        else:
            print("error, unsupported signedness")
            exit(0)

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
    if prover == "cvc5sys":
        cmd = ["./bin_solvers/bin/cvc5-Linux", filename]
        solve_with_bin_solver(cmd, g_verifier_args.timeout)
        return
    all_vars, init, trans, post = parse_sygus(filename, to_real_type=False)
    print("Finish parsing SyGuS file")
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])
    if sts.has_bv:
        # TODO: enforce to add this (or, infer automatically)
        #  e.g., check whether there are bvsle, bvslt, ... in the formula
        if g_verifier_args.signedness == "signed":
            sts.set_signedness("signed")
        elif g_verifier_args.signedness == "unsigned":
            sts.set_signedness("unsigned")
        else:
            print("error, unsupported signedness")
            exit(0)

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
    global g_verifier_args
    import argparse

    setup_signal_handlers()

    # dir_path = os.path.dirname(os.path.realpath(__file__))
    # fib_04.sl needs disjunctive?
    # solve_sygus_file(dir_path + '/benchmarks/sygus-inv/LIA/2017.ASE_FiB/fib_01.sl', "efsmt")
    # solve_chc_file(dir_path + '/benchmarks/chc/bv/2017.ASE_FIB/32bits_signed/fib_15.sl_32bits_signed.smt2',
    #               prover="efsmt")
    # exit(0)
    parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
    
    # Core arguments
    parser.add_argument('--file', dest='file', default='none', type=str, help="Path to the input file")
    parser.add_argument('--engine', dest='engine', default='efsmt', type=str, help='''Set the engine:
  efsmt: template-based invariant generation + efsmt solving;
  pdr: property-directed reachability (we use the engine inside Z3);
  kind: k-induction''')
    parser.add_argument('--lang', dest='lang', default='sygus', type=str, help="The input format: sygus or chc")
    parser.add_argument('--timeout', dest='timeout', default=3000, type=int, help="timeout")
    parser.add_argument('--verbose', dest='verbosity', default=1, type=int, help='verbosity level')
    parser.add_argument('--signedness', dest='signedness', default='signed', type=str,
                        help="The signedness of the bit-vector variables (signed or unsigned)")

    # EFSMT engine options
    efsmt_group = parser.add_argument_group('EFSMT engine options')
    efsmt_group.add_argument('--template', dest='template', default='interval', type=str,
                        help="The invariant template")
    efsmt_group.add_argument('--num-disjunctions', dest='num_disjunctions', default=1, type=int,
                        help="Set the number of disjunctions (for disjunctive invariant)")
    efsmt_group.add_argument('--prevent-over-under-flows', dest='prevent_over_under_flows', default=0, type=int,
                        help="Preventing over/under flows in the template expressions")
    efsmt_group.add_argument('--prop-strengthen', dest='prop_strengthen', default=False, action='store_true',
                        help="Enable property strengthening using 'T = T and Prop' as template")
    efsmt_group.add_argument('--validate-invariant', dest='validate_invariant', default=False, action='store_true',
                        help="Validate the correctness of the invariant")
    
    # EFSMT solver options
    efsmt_group.add_argument('--efsmt-solver', dest='efsmt_solver', default='z3api', type=str, 
                        help="Solver for the exists-forall SMT problem. Options include:\n"
                             "1. Quantifier instantiation approach: [z3, cvc5, btor, yices2, mathsat, bitwuzla, z3api]\n"
                             "2. Bit-blasting approach: [z3qbf, caqe, q3b, z3sat]\n"
                             "3. CEGIS approach: [cegis] (implemented via pysmt, need to set pysmt_solver)")
    efsmt_group.add_argument('--pysmt-solver', dest='pysmt_solver', default="z3", type=str,
                        help="Set the PySMT solver for the CEGIS solver's backend. Options include: [z3, cvc5, btor, yices2, mathsat, bitwuzla]")

    # Constraint dumping options (EFSMT related)
    dump_group = parser.add_argument_group('EFSMT constraint dumping options')
    dump_group.add_argument('--dump-ef-smt2', dest='dump_ef_smt2', default=False, action='store_true',
                        help="Dump the quantified SMT2 constraint")
    dump_group.add_argument('--dump-qbf', dest='dump_qbf', default=False, action='store_true',
                        help="Dump the quantified QBF constraint")
    dump_group.add_argument('--dump-cnt-dir', dest='dump_cnt_dir', default="/tmp", type=str,
                        help="The dir for storing the dumped constraints")

    # K-induction engine options
    kind_group = parser.add_argument_group('K-induction engine options')
    kind_group.add_argument('--kind-k', dest='kind_k', default=30, type=int,
                        help="Set the k value for k-induction (default: 30)")
    kind_group.add_argument('--kind-incremental', dest='kind_incremental', default=False, action='store_true',
                        help="Use incremental k-induction (default: False)")
    kind_group.add_argument('--kind-parallel-workers', dest='kind_parallel_workers', default=1, type=int,
                        help="Set the number of parallel workers for k-induction (default: 1)")
    kind_group.add_argument('--kind-multi-properties-alg', dest='kind_multi_properties_alg',
                            default='default', type=str, help="Select the approach for multiple properties. "
                                                              "Options include: [default, parallel]")
    kind_group.add_argument('--kind-aux-inv', dest='kind_aux_inv', default=False, action='store_true',
                        help="Use aux invariant for k-induction (default: False)")
    kind_group.add_argument('--kind-aux-inv-alg', dest='kind_aux_inv_alg', default='default', type=str,
                            help="Select the approach for generating auxiliary invariants. Options include: [top, int]")

    # PDR engine options
    # Allow for parsing options to Z3's PDR engine (named Spacer)
    # FIXME: refer to the Z3 documentation for the options
    pdr_group = parser.add_argument_group('PDR engine options')


    g_verifier_args = parser.parse_args()

    if g_verifier_args.verbosity == 2:
        logging.basicConfig(level=logging.DEBUG)

    if g_verifier_args.file == 'none':
        print("Please provide an input file using --file")
        parser.print_help()
        exit(0)

    if g_verifier_args.lang == "sygus":
        solve_sygus_file(g_verifier_args.file, g_verifier_args.engine)
    elif g_verifier_args.lang == "chc":
        solve_chc_file(g_verifier_args.file, g_verifier_args.engine)
    else:
        print("Not supported format {}".format(g_verifier_args.lang))
        exit(0)
