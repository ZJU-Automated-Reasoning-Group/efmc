"""Command-line interface for EFMC (Enhanced Formal Model Checker)
This module provides the main CLI interface for running different verification engines
on transition systems specified in various formats.
"""

import argparse
import logging
import os
import signal
import sys
from pathlib import Path
from typing import List

import psutil

from efmc.engines.ef.ef_prover import EFProver
from efmc.engines.kinduction.kind_prover import KInductionProver
from efmc.engines.pdr.pdr_prover import PDRProver
from efmc.engines.qe import QuantifierEliminationProver
from efmc.frontends import parse_sygus, parse_chc
from efmc.sts import TransitionSystem
from efmc.utils.global_config import g_verifier_args


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
            if "bv" not in g_verifier_args.template:
                self.logger.error(f"Unsupported template: {g_verifier_args.template}")
                self.logger.info(f"Available templates: {TEMPLATES['bitvector']}")
                sys.exit(1)

            ef_prover = EFProver(
                sts,
                prop_strengthen=g_verifier_args.prop_strengthen,
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
                validate_invariant=g_verifier_args.validate_invariant,
                pysmt_solver=g_verifier_args.pysmt_solver
            )
            
            if g_verifier_args.template in TEMPLATES['int_real']:
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
        if g_verifier_args.engine == "eld":
            eld_path = str(Path(__file__).parent.parent.parent / "bin_solvers/bin/eld")
            cmd = [eld_path, filename]
            # Use subprocess to run eld
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
            "qe": self.run_qe
        }
        
        if g_verifier_args.engine not in engine_map:
            self.logger.error(f"Unsupported engine: {g_verifier_args.engine}")
            self.logger.info(f"Available engines: {list(engine_map.keys())}")
            sys.exit(1)
            
        engine_map[g_verifier_args.engine](sts)

def parse_arguments():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(description='EFMC - Enhanced Formal Model Checker')
    
    parser.add_argument('--file', type=str, required=True,
                      help='Input file to verify')
    
    parser.add_argument('--lang', type=str, choices=['chc', 'sygus'],
                      default='sygus', help='Input language format')
    
    parser.add_argument('--engine', type=str, 
                      choices=['ef', 'pdr', 'kind', 'qe', 'eld'],
                      default='ef', help='Verification engine to use')
    
    parser.add_argument('--template', type=str,
                      help='Template for invariant generation')
    
    parser.add_argument('--efsmt-solver', type=str, default='z3',
                      help='SMT solver for EFSMT')
    
    parser.add_argument('--pysmt-solver', type=str, default='z3',
                      help='PySMT solver to use')
    
    parser.add_argument('--prop-strengthen', action='store_true',
                      help='Enable property strengthening')
    
    parser.add_argument('--validate-invariant', action='store_true',
                      help='Validate generated invariants')
    
    parser.add_argument('--prevent-over-under-flows', type=int, default=0,
                      help='Prevent over/underflows in bitvector operations')
    
    parser.add_argument('--num-disjunctions', type=int, default=1,
                      help='Number of disjunctions in template')
    
    parser.add_argument('--kind-k', type=int, default=1,
                      help='K value for k-induction')
    
    parser.add_argument('--kind-aux-inv', action='store_true',
                      help='Use auxiliary invariants in k-induction')
    
    parser.add_argument('--signedness', type=str,
                      choices=['signed', 'unsigned'],
                      help='Signedness for bitvector operations')
    
    parser.add_argument('--dump-ef-smt2', action='store_true',
                      help='Dump EF constraints in SMT2 format')
    
    parser.add_argument('--dump-qbf', action='store_true',
                      help='Dump constraints in QBF format')

    return parser.parse_args()

def main():
    """Main entry point for the CLI"""
    global g_verifier_args
    g_verifier_args = parse_arguments()
    
    runner = EFMCRunner()
    
    if g_verifier_args.lang == "chc":
        runner.verify_chc(g_verifier_args.file)
    elif g_verifier_args.lang == "sygus":
        runner.verify_sygus(g_verifier_args.file)
    else:
        runner.logger.error(f"Unsupported input language: {g_verifier_args.lang}")
        runner.logger.info("Supported languages: chc, sygus")
        sys.exit(1)


if __name__ == "__main__":
    main()
