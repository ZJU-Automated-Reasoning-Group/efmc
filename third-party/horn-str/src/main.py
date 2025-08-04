#!/bin/env python3

import argparse
from chc import *

solver_list = [
    "ostrich",
    "ostrich-regex",
    "ostrich-fwd",
    "ostrich-fwd-regex",
    "z3",
    "z3-alpha",
    "z3-noodler",
    "cvc4",
    "cvc5",
]
sat_solver_list = [
    "ostrich",
    "ostrich-regex",
    "ostrich-fwd",
    "ostrich-fwd-regex",
    "z3",
    "z3-alpha",
    "z3-noodler",
    "cvc4",
    "cvc5",
]
transducer_list = ["unification", "interleaving", "concatenation", "both"]
parser = argparse.ArgumentParser(
    description="Check sat of a SMT2 file in" + "SMT2 format."
)
parser.add_argument("fname")
parser.add_argument("--debug", "-d", action="store_true")
parser.add_argument("--learner-debug", "-ld", action="store_true")

parser.add_argument("--linear", "-lr", action="store_true")
parser.add_argument(
    "--monadic",
    "-mon",
    action="store_true",
    default=False,
    help="Use monadic predicates (def: False)",
)

parser.add_argument(
    "--least",
    "-l",
    action="store_true",
    default=False,
    help="Prioritize learning the reachable fragment/lfp (def: False, gfp/safety)",
)
parser.add_argument(
    "--approx",
    "-a",
    type=int,
    default=None,
    help="approximate reachability",
)
parser.add_argument(
    "--params_num",
    "-ps",
    type=int,
    default=1,
    help="number of parameters for the predicate",
)
parser.add_argument(
    "--invs_num",
    "-invs",
    type=int,
    default=1,
    help="number of the predicate",
)
parser.add_argument(
    "--solver",
    choices=solver_list,
    help=f"SMT solver (from list {', '.join(solver_list)})",
)
parser.add_argument(
    "--sat_solver",
    choices=solver_list,
    default="z3",
    help=f"SMT solver (from list {', '.join(solver_list)})",
)
parser.add_argument(
    "--solver-mem",
    choices=solver_list,
    help=f"Override SMT solver for MEM queries only",
)
parser.add_argument(
    "--method",
    choices=["lstar", "sat", "sfa-learning"],
)

parser.add_argument(
    "--method-args", nargs='*', help='Arguments of the --method used. The arguments are passed to the method'
                                    'which in turn can do whatever it wants with them, maybe disregard them.'
)

parser.add_argument(
    "--group-oracles",
    choices=["no", "by-type", "all"],
    default="no",
    help="Group all equivalence oracles into one single (default: no), "
    + "or several oracles, one per clause type (inductive, init and block).",
)
parser.add_argument(
    "--transducer",
    choices=transducer_list,
    help=f"Transducer type (from list {', '.join(transducer_list)})",
)

if __name__ == "__main__":
    args = parser.parse_args()
    if args.fname:
        if not os.path.exists(args.fname):
            print(f"File {args.fname} does not exist. Maybe you misspelled it?")
            exit(1)

    s = CHCStrSolver(
        args.fname,
        debug=args.debug,
        learner_debug=args.learner_debug,
        solver=args.solver or solver_list[0],
        solver_mem=args.solver_mem or args.solver or solver_list[0],
        group_oracles=args.group_oracles,
        transducer=args.transducer,
        method_arguments=args.method_args
    )
    if args.method == "lstar":
        s.check_lstar_based(greatest=not args.least, approx=args.approx)
    elif args.method == "sfa-learning":
        s.check_sfa_passive_learning(greatest=not args.least, approx=args.approx)
    elif args.method == "sat": # this is also the default, but let's call it explicitly for now
        s.check_sat_based(args.sat_solver, debug=args.debug, name=args.fname)
    else:
        s.check_sat_based(args.sat_solver, debug=args.debug, name=args.fname)
