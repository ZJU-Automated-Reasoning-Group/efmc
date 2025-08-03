#!/usr/bin/env python3
"""
EFMC-Term: CLI for termination/non-termination proving (bit-vector programs).
"""
import argparse
import logging
import sys
from typing import Dict, Any

from efmc.frontends import parse_chc, parse_sygus
from efmc.sts import TransitionSystem
from efmc.engines.ef.termination import (
    prove_termination_with_ranking_functions,
    prove_non_termination_with_recurrence_sets,
    analyze_termination
)

def parse_arguments() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="EFMC-Term: Termination/Non-Termination Prover for Bit-Vector Programs")
    p.add_argument('--file', type=str, required=True, help='Input file to verify')
    p.add_argument('--lang', type=str, choices=['chc', 'sygus', 'auto'], default='auto', help='Input language format')
    p.add_argument('--log-level', type=str, choices=['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL'], default='INFO')
    p.add_argument('--mode', type=str, choices=['termination', 'nontermination', 'analyze'], default=None, help='What to prove. If not set, tries termination then non-termination sequentially.')
    p.add_argument('--ranking-template', type=str, nargs='+', default=None, help='Ranking template(s): bv_linear_ranking, bv_lexicographic_ranking, bv_conditional_ranking')
    p.add_argument('--recurrence-template', type=str, nargs='+', default=None, help='Recurrence template(s): bv_linear_recurrence, bv_interval_recurrence, bv_disjunctive_recurrence')
    p.add_argument('--num-components', type=int, default=2)
    p.add_argument('--num-branches', type=int, default=2)
    p.add_argument('--num-disjuncts', type=int, default=2)
    p.add_argument('--base-template-type', type=str, default='interval', choices=['interval', 'linear'])
    p.add_argument('--solver', type=str, default='z3api')
    p.add_argument('--timeout', type=int, default=60)
    p.add_argument('--signedness', type=str, default='signed', choices=['signed', 'unsigned'])
    p.add_argument('--validate', action='store_true')
    p.add_argument('--print-vc', action='store_true')
    return p.parse_args()

def print_result(result: Dict[str, Any]) -> None:
    if result.get('termination_proven'):
        print("Result: TERMINATION PROVEN")
        if result.get('ranking_function') is not None:
            print("Ranking function:\n", result['ranking_function'])
        print(f"Template used: {result.get('ranking_template_used')}")
    elif result.get('non_termination_proven'):
        print("Result: NON-TERMINATION PROVEN")
        if result.get('recurrence_set') is not None:
            print("Recurrence set:\n", result['recurrence_set'])
        print(f"Template used: {result.get('recurrence_template_used')}")
    else:
        print("Result: UNKNOWN (could not prove termination or non-termination)")
        if result.get('errors'):
            print("Errors:", *result['errors'], sep='\n  - ')

def build_transition_system(args: argparse.Namespace) -> TransitionSystem:
    if args.lang == 'chc' or (args.lang == 'auto' and args.file.endswith('.smt2')):
        all_vars, init, trans, post = parse_chc(args.file, to_real_type=False)
    elif args.lang == 'sygus' or (args.lang == 'auto' and args.file.endswith('.sl')):
        all_vars, init, trans, post = parse_sygus(args.file, to_real_type=False)
    else:
        print(f"Unsupported file extension or language: {args.file}"); sys.exit(1)
    sts = TransitionSystem(); sts.from_z3_cnts([all_vars, init, trans, post])
    if sts.has_bv and args.signedness in ['signed', 'unsigned']:
        sts.set_signedness(args.signedness)
    return sts

def run_mode(args: argparse.Namespace, sts: TransitionSystem, prover_kwargs: Dict[str, Any]) -> None:
    if args.mode == 'termination':
        ok, ranking_func, template_used = prove_termination_with_ranking_functions(
            sts, template_names=args.ranking_template, timeout=args.timeout, **prover_kwargs)
        result = {'termination_proven': ok, 'ranking_function': ranking_func, 'ranking_template_used': template_used, 'errors': [] if ok else ["Could not prove termination"]}
    elif args.mode == 'nontermination':
        ok, recurrence_set, template_used = prove_non_termination_with_recurrence_sets(
            sts, template_names=args.recurrence_template, timeout=args.timeout, **prover_kwargs)
        result = {'non_termination_proven': ok, 'recurrence_set': recurrence_set, 'recurrence_template_used': template_used, 'errors': [] if ok else ["Could not prove non-termination"]}
    elif args.mode == 'analyze':
        result = analyze_termination(
            sts, ranking_templates=args.ranking_template, recurrence_templates=args.recurrence_template, timeout=args.timeout, **prover_kwargs)
    else:
        ok, ranking_func, template_used = prove_termination_with_ranking_functions(
            sts, template_names=args.ranking_template, timeout=args.timeout, **prover_kwargs)
        if ok:
            result = {'termination_proven': ok, 'ranking_function': ranking_func, 'ranking_template_used': template_used, 'errors': []}
        else:
            ok2, recurrence_set, template_used2 = prove_non_termination_with_recurrence_sets(
                sts, template_names=args.recurrence_template, timeout=args.timeout, **prover_kwargs)
            if ok2:
                result = {'non_termination_proven': ok2, 'recurrence_set': recurrence_set, 'recurrence_template_used': template_used2, 'errors': []}
            else:
                result = {'termination_proven': False, 'non_termination_proven': False, 'errors': ["Could not prove termination or non-termination"]}
    print_result(result)

def main() -> None:
    args = parse_arguments()
    logging.basicConfig(level=getattr(logging, args.log_level), format='%(asctime)s - %(levelname)s - %(message)s')
    sts = build_transition_system(args)
    prover_kwargs = {
        'solver': args.solver,
        'validate_ranking_function': args.validate,
        'validate_recurrence_set': args.validate,
        'num_components': args.num_components,
        'num_branches': args.num_branches,
        'num_disjuncts': args.num_disjuncts,
        'base_template_type': args.base_template_type,
        'print_vc': args.print_vc,
    }
    run_mode(args, sts, prover_kwargs)

if __name__ == "__main__":
    main()
