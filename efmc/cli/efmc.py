"""Command-line interface for EFMC.
This module provides the main CLI interface for running different verification engines
on transition systems specified in various formats.
"""

import argparse
import logging
import os
import signal
import sys
from pathlib import Path
import logging
import subprocess
from threading import Timer
from typing import List
import psutil

from efmc.frontends import parse_sygus, parse_chc
from efmc.sts import TransitionSystem
from efmc.efmc_config import g_verifier_args, update_config_from_globals

from efmc.engines.ef import EFProver
from efmc.engines.kinduction import KInductionProver
from efmc.engines.pdr import PDRProver
from efmc.engines.qe import QuantifierEliminationProver
from efmc.engines.qi import QuantifierInstantiationProver
from efmc.engines.houdini import HoudiniProver

# Available templates
TEMPLATES = {
    'int_real': [
        "interval", "power_interval",
        "zone", "octagon",
        "affine", "power_affine",
        "poly", "power_poly"
    ],
    'bitvector': [
        "bv_interval", "power_bv_interval",
        "bv_zone", "power_bv_zone",
        "bv_octagon", "power_bv_octagon",
        "bv_poly", "power_bv_poly"
    ]
}


def solve_with_bin_verifier(cmd: List[str], timeout=3600) -> str:
    """ cmd should be a complete cmd"""
    is_timeout = [False]

    p = subprocess.Popen(cmd, stderr=subprocess.STDOUT)
    timer = Timer(timeout, terminate, args=[p, is_timeout])
    timer.start()
    p.wait()
    timer.cancel()


class EFMCRunner:
    """Main runner class for EFMC verification tasks"""
    
    def __init__(self):
        self.logger = logging.getLogger(__name__)
        self.setup_signal_handlers()

    def setup_signal_handlers(self):
        """Configure signal handlers for graceful termination"""
        def handler(sig, frame):
            self.logger.info("Handling termination signal")
            parent = psutil.Process(os.getpid())
            for child in parent.children(recursive=True):
                child.kill()
            sys.exit(0)

        for sig in [signal.SIGINT, signal.SIGQUIT, signal.SIGABRT, signal.SIGTERM]:
            signal.signal(sig, handler)

    def run_ef_prover(self, sts: TransitionSystem) -> None:
        """Run template-based invariant generation using EF prover"""
        if sts.has_bv:
            if g_verifier_args.template == "auto":
                g_verifier_args.template = "bv_interval"
            elif "bv" not in g_verifier_args.template:
                self.logger.error(f"Unsupported template: {g_verifier_args.template}")
                self.logger.info(f"Available templates: {TEMPLATES['bitvector']}")
                sys.exit(1)
            else:
                self.logger.error(f"Unsupported template: {g_verifier_args.template}")
                sys.exit(1)

            ef_prover = EFProver(
                sts,
                prop_strengthen=g_verifier_args.prop_strengthen,
                abs_refine=g_verifier_args.abs_refine,
                validate_invariant=g_verifier_args.validate_invariant,
                no_overflow=g_verifier_args.prevent_over_under_flows > 0,
                no_underflow=g_verifier_args.prevent_over_under_flows > 0,
                pysmt_solver=g_verifier_args.pysmt_solver
            )
            
            if g_verifier_args.template in TEMPLATES['bitvector']:
                ef_prover.set_template(g_verifier_args.template, 
                                     num_disjunctions=g_verifier_args.num_disjunctions)
                ef_prover.set_solver(g_verifier_args.efsmt_solver)
            else:
                self.logger.error(f"Unsupported template: {g_verifier_args.template}")
                self.logger.info(f"Available templates: {TEMPLATES['bitvector']}")
                sys.exit(1)
        else:
            ef_prover = EFProver(
                sts,
                prop_strengthen=g_verifier_args.prop_strengthen,
                abs_refine=g_verifier_args.abs_refine,
                validate_invariant=g_verifier_args.validate_invariant,
                pysmt_solver=g_verifier_args.pysmt_solver
            )

            if g_verifier_args.template == "auto":
                ef_prover.set_template("interval")
                ef_prover.set_solver(g_verifier_args.efsmt_solver)        
            elif g_verifier_args.template in TEMPLATES['int_real']:
                ef_prover.set_template(g_verifier_args.template,
                                     num_disjunctions=g_verifier_args.num_disjunctions)
                ef_prover.set_solver(g_verifier_args.efsmt_solver)
            else:
                self.logger.error(f"Unsupported template: {g_verifier_args.template}")
                self.logger.info(f"Available templates: {TEMPLATES['int_real']}")
                sys.exit(1)

        if g_verifier_args.dump_ef_smt2 or g_verifier_args.dump_qbf:
            ef_prover.dump_constraint(g_verifier_args)
        else:
            res = ef_prover.solve()
            print("safe" if res == "sat" else "unknown")

    def run_pdr(self, sts: TransitionSystem) -> None:
        """Run PDR/IC3 verification"""
        pdr_prover = PDRProver(sts)
        pdr_prover.solve()

    def run_qi(self, sts: TransitionSystem) -> None:
        """Run the Quantifier Instantiation (QI) based verification"""
        qi_prover = QuantifierInstantiationProver(sts)
        
        # Set the QI strategy based on the command-line argument
        if hasattr(g_verifier_args, 'qi_strategy'):
            qi_prover.set_strategy(g_verifier_args.qi_strategy)
            self.logger.info(f"Using QI strategy: {g_verifier_args.qi_strategy}")
        
        qi_prover.solve()

    def run_k_induction(self, sts: TransitionSystem) -> None:
        """Run k-induction verification"""
        self.logger.info("Starting k-induction...")
        kind_prover = KInductionProver(sts)
        if g_verifier_args.kind_aux_inv:
            kind_prover.use_aux_invariant = True
        kind_prover.solve(int(g_verifier_args.kind_k))

    def run_qe(self, sts: TransitionSystem) -> None:
        """Run quantifier elimination based verification"""
        qe_prover = QuantifierEliminationProver(sts)
        qe_prover.solve()

    def verify_chc(self, filename: str) -> None:
        """Verify CHC format file"""
        if g_verifier_args.use_eld:
            eld_path = str(Path(__file__).parent.parent.parent / "bin_solvers/bin/eld")
            cmd = [eld_path, filename]
            solve_with_bin_verifier(cmd, g_verifier_args.timeout)
            return

        all_vars, init, trans, post = parse_chc(filename, to_real_type=False)
        self.logger.info("CHC file parsing completed")
        
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        
        if sts.has_bv and g_verifier_args.signedness in ["signed", "unsigned"]:
            sts.set_signedness(g_verifier_args.signedness)
            
        self.run_verifier(sts)

    def verify_sygus(self, filename: str) -> None:
        """Verify SyGuS format file"""
        
        # it is not a good idea to use the "engine" option
        if g_verifier_args.use_cvc5sy:
            from efmc.efmc_config import cvc5_exec
            cmd = [cvc5_exec, filename]
            solve_with_bin_verifier(cmd, g_verifier_args.timeout)
            return

        all_vars, init, trans, post = parse_sygus(filename, to_real_type=False)
        self.logger.info("SyGuS file parsing completed")
        
        sts = TransitionSystem()
        sts.from_z3_cnts([all_vars, init, trans, post])
        
        if sts.has_bv and g_verifier_args.signedness in ["signed", "unsigned"]:
            sts.set_signedness(g_verifier_args.signedness)
            
        self.run_verifier(sts)

    def run_verifier(self, sts: TransitionSystem) -> None:
        """Run the selected verification engine"""
        engine_map = {
            "ef": self.run_ef_prover,
            "pdr": self.run_pdr,
            "kind": self.run_k_induction,
            "qe": self.run_qe,
            "qi": self.run_qi,
            "houdini": self.run_houdini  # Add Houdini engine
        }
        
        if g_verifier_args.engine not in engine_map:
            self.logger.error(f"Unsupported engine: {g_verifier_args.engine}")
            self.logger.info(f"Available engines: {list(engine_map.keys())}")
            sys.exit(1)
            
        engine_map[g_verifier_args.engine](sts)

    def run_houdini(self, sts: TransitionSystem) -> None:
        """Run Houdini-based invariant inference"""
        houdini_prover = HoudiniProver(sts)
        res = houdini_prover.solve()
        print("safe" if res == "safe" else "unknown")

def parse_arguments():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(description='EFMC - A Software Model Checker')
    
    # Input and general options
    input_group = parser.add_argument_group('Input options')
    input_group.add_argument('--file', type=str, required=True,
                      help='Input file to verify')
    input_group.add_argument('--lang', type=str, choices=['chc', 'sygus', 'auto'],
                      default='auto', help='Input language format')
    input_group.add_argument('--engine', type=str, 
                      choices=['ef', 'pdr', 'kind', 'qe', 'eld', 'qi', 'houdini'],
                      default='ef', help='Verification engine to use')
    input_group.add_argument('--log-level', type=str, 
                      choices=['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL'],
                      default='INFO', help='Set the logging level')

    # Template-based verification options
    template_group = parser.add_argument_group('Template-based verification options')
    template_group.add_argument('--template', type=str, default="auto",
                      help='Template for invariant generation. For integer/real: interval, power_interval, zone, octagon, affine, power_affine, poly, power_poly. For bitvector: bv_interval, power_bv_interval, bv_zone, power_bv_zone, bv_octagon, power_bv_octagon, bv_poly, power_bv_poly')
    template_group.add_argument('--num-disjunctions', type=int, default=1,
                      help='Number of disjunctions in template')
    template_group.add_argument('--prop-strengthen', action='store_true',
                      help='Enable property strengthening')
    template_group.add_argument('--abs-refine', action='store_true',
                      help='Enable abstraction refinement')
    template_group.add_argument('--validate-invariant', action='store_true',
                      help='Validate generated invariants')

    # Solver options
    # currently, only affect the ef engine?
    solver_group = parser.add_argument_group('Solver options')

    # "z3api" means we use the z3py API to solve the constraints "in memory"
    solver_group.add_argument('--efsmt-solver', type=str, default='z3api',
                      help='The solver to use for EFSMT solving')
    solver_group.add_argument('--pysmt-solver', type=str, default='z3',
                      help='SMT solver for the CEGIS-based EFSMT solving (implemented via pysmt)')

    # Currently, the timeout is not used for the engines inside efmc
    # It is better to control the timeout in some "upper-level" scripts.
    # solver_group.add_argument('timeout', type=int, default=5,
    #                      help='Timeout in seconds for the verification engine')
    
    # Bitvector options
    bv_group = parser.add_argument_group('Bitvector options')
    bv_group.add_argument('--prevent-over-under-flows', type=int, default=0,
                      help='Prevent over/underflows in bitvector operations')
    bv_group.add_argument('--signedness', type=str, default='signed',
                      choices=['signed', 'unsigned'],
                      help='Signedness for bitvector operations')
    
    # Output options
    output_group = parser.add_argument_group('EFSMT constraint dumping options')
    output_group.add_argument('--dump-ef-smt2', action='store_true', default=False,
                      help='Dump EF constraints in SMT2 format')
    output_group.add_argument('--dump-qbf', action='store_true', default=False,
                      help='Dump constraints in QBF format')
    output_group.add_argument('--dump-cnt-dir', dest='dump_cnt_dir', default="/tmp", type=str, help="The dir for storing the dumped constraints")

    # K-induction options
    kind_group = parser.add_argument_group('K-induction options')
    kind_group.add_argument('--kind-k', type=int, default=1,
                      help='K value for k-induction')
    kind_group.add_argument('--kind-incremental', dest='kind_incremental', default=False, action='store_true',
                        help="Use incremental k-induction (default: False)")
    kind_group.add_argument('--kind-aux-inv', action='store_true',
                      help='Use auxiliary invariants in k-induction')
    kind_group.add_argument('--kind-aux-inv-alg', dest='kind_aux_inv_alg', default='default', type=str,
                            help="Select the approach for generating auxiliary invariants. Options include: [top, int, houdini]")

    # Quantifier instantiation-based verification options
    qi_group = parser.add_argument_group('Quantifier instantiation-based verification options')
    qi_group.add_argument('--qi-strategy', type=str, default='mbqi',
                      help='Quantifier instantiation strategy (mbqi, ematching, combined, auto)')

    # PDR engine options: Allow for parsing options to Z3's PDR engine (named Spacer)
    # FIXME: refer to the Z3 documentation for the options
    # pdr_group = parser.add_argument_group('PDR engine options')

    # third-party, binary verifiers
    third_party_group = parser.add_argument_group('Third-party binary verifiers')
    third_party_group.add_argument('--use-eld', type=bool, default=False,
                      help='Use Eldrica (for CHC)')
    third_party_group.add_argument('--use-cvc5sy', type=bool, default=False,
                      help='Use cvc4sy (for SyGuS)')

    return parser.parse_args()

def main():
    """Main entry point for the CLI"""
    global g_verifier_args
    g_verifier_args = parse_arguments()
    
    # Configure logging based on the specified log level
    logging.basicConfig(
        level=getattr(logging, g_verifier_args.log_level),
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )
    
    update_config_from_globals()
    
    runner = EFMCRunner()

    if g_verifier_args.lang == "chc":
        runner.verify_chc(g_verifier_args.file)
    elif g_verifier_args.lang == "sygus":
        runner.verify_sygus(g_verifier_args.file)
    else:  # the default value is "auto"
        file_extension = os.path.splitext(g_verifier_args.file)[1].lower()
        if file_extension == '.smt2':
            runner.verify_chc(g_verifier_args.file)
        elif file_extension == '.sy':
            runner.verify_sygus(g_verifier_args.file)
        else:
            logging.error(f"Unsupported file extension: {file_extension}")
            logging.info("Supported extensions: .smt2 (CHC), .sy (SyGuS)")
            sys.exit(1)



if __name__ == "__main__":
    main()
