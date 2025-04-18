#!/usr/bin/python

import os
import sys
import copy
import tempfile
import splitter

def prove_terminates(filename):
  splitfile = tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False)
  (id_map, has_nested, nondet) = splitter.split(filename, splitfile)
  nids = len(id_map)
  varnames = ' '.join(id_map[k] for k in range(nids))

  splitfile.close()

  os.system(("kalashnikov.py " +
             "%s ../../tests/termination/unranking.c " +
             "-P2 " +
             "--synth-strategy=genetic " +
             "-c1 " +
             "--fastverif=True " +
             "-newsize=5 " +
             "-replaceprob=0.15 " +
             "-mutprob=0.1 " +
             "-tourneysize=5 " +
             "-popsize=3000 " +
             "-w4 " +
             "-a%d --evars %d --varnames %s --resnames I --seed=1337 " +
             "--nondet=%d " +
             "%s") % 
              (splitfile.name,
                nids,
                nids,
                varnames,
                nondet,
                ' '.join(sys.argv[2:])))

if __name__ == '__main__':
  import sys

  try:
    os.unlink("/tmp/geneticsynth")
  except:
    pass

  try:
    os.unlink("/tmp/annealsynth")
  except:
    pass

  prove_terminates(sys.argv[1])
