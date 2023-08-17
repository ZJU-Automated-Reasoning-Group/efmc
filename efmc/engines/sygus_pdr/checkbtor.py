
import argparse
from pathlib import Path

from efmc.engines.sygus_pdr.btorparser import BTOR2Parser
from efmc.engines.sygus_pdr.pdr import PDR


def filter_varset(allvars, varfile, modulename):
    include_set = set()
    exclude_set = set()
    if varfile:
        with open(varfile) as varfin:
            l = varfin.readline()
            while l:
                if l.startswith('EXCLUDE:'):
                    for e in l[8:].split(','):
                        exclude_set.add(e.strip())
                elif l.startswith('INCLUDE:'):
                    for e in l[8:].split(','):
                        include_set.add(e.strip())
                l = varfin.readline()
    final_keep_vars = set()
    final_remove_vars = set()
    for v in allvars:
        n = v.symbol_name()
        if modulename and not n.startswith(modulename + '.'):
            final_remove_vars.add(v)
        elif n in exclude_set:
            final_remove_vars.add(v)
        elif len(include_set) > 0 and n not in include_set:
            final_remove_vars.add(v)
        else:  # it is in the include_set or include_set is empty
            final_keep_vars.add(v)
    return final_keep_vars, final_remove_vars


def check(btorfname, varfile, modulename, outputfile):  # will need to dump inv/result to file
    btor_parser = BTOR2Parser()
    sts, _ = btor_parser.parse_file(Path(btorfname))
    # generate varset
    keep_vars, remove_vars = filter_varset(sts.variables, varfile, modulename)

    pdr_checker = PDR(sts)
    if not pdr_checker.check_property(sts.assertion, remove_vars=remove_vars, keep_vars=keep_vars):
        print('FAIL!')
        return

    pdr_checker.sanity_check_imply()
    pdr_checker.sanity_check_frame_monotone()
    pdr_checker.sanity_check_safe_inductive_inv(sts.assertion)
    pdr_checker.dump_frames()
    print('SUCCEED: ', pdr_checker.get_inv_str())
    if outputfile:
        with open(outputfile, 'w') as fout:
            fout.write(pdr_checker.get_inv().to_smtlib(daggify=False))


def main():
    parser = argparse.ArgumentParser(description='PDR on btor2')
    parser.add_argument('file', help='btor2 input')
    parser.add_argument('-o', '--output', help='result and invariants file')
    parser.add_argument('-m', '--module', help='restrict varset to this module')
    parser.add_argument('-v', '--varset', help='additional varset restriction')
    # variable file: INCLUDE: ',' separated file
    # EXCLUDE: ',' separated file
    parser.add_argument('-c', '--config', help='load configuration from this file')
    args = parser.parse_args()

    check(args.file, args.varset, args.module, args.output)


if __name__ == '__main__':
    main()