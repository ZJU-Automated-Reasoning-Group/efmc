#!/usr/bin/python3

import sys, getopt, logging
from game import Game
from pysmt.shortcuts import is_sat


def main(argv):
    inputfile = ''
    usage = 'Usage: cab.py -i <inputfile> [options]'
    options = ('Options are:\n\t--debug, -d \n\t\ttoggles printing of debug messages.\n\t' +
               '--smtinterpol\n\t\ttoggles usage of smtinterpol solver for interpolation.')
    man = '%s\n\n%s' % (usage, options)

    try:
        opts, args = getopt.getopt(argv, 'hi:d', ['input=', 'debug'])
    except getopt.GetoptError:
        print(man)
        sys.exit(2)

    for opt, arg in opts:
        if opt == '-h':
            print(man)
            sys.exit(2)
        elif opt in ('-i', '--input'):
            inputfile = arg
        elif opt in ('-d', '--debug'):
            logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)

    if logging.DEBUG < logging.root.level:
        logging.basicConfig(level=logging.WARNING)

    g = Game.read(inputfile)
    res, n = g.solve(0)
    if is_sat(res):
        print('Player REACH wins.')
    else:
        print('Player SAFE wins.')
    print('Number of visited subgames: ' + str(n))


if __name__ == "__main__":
    main(sys.argv[1:])
