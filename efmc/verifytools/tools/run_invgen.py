#! /usr/bin/env python
from efmc.verifytools.tools.levels import loadBoogieLvlSet
import argparse
from efmc.verifytools.tools.vc_check import tryAndVerifyLvl
from efmc.verifytools.invgen import runInvGen, convertCppFileForInvGen
from efmc.verifytools.boogie.ast import parseExprAst
from efmc.verifytools.common.util import error
from os.path import exists
import re

def parseInvGenInvariant(inv):
  replaceEq = re.compile("([^<>=])=([^<>=])")
  inv = replaceEq.sub(r"\1==\2", inv)
  inv = inv.replace("=<", "<=")
  return parseExprAst(inv)

if (__name__ == "__main__"):
  p = argparse.ArgumentParser(description="run invgen on a levelset")
  p.add_argument('--lvlset', type=str, \
          help='Path to lvlset file', required=True)
  p.add_argument('--time-limit', type=int, \
          help='Timeout for any operation involving InvGen or z3')
  p.add_argument('--csv-table', action="store_true", default=False, \
          help='Print results as a csv table')
  args = p.parse_args();

  lvlSetName, lvls = loadBoogieLvlSet(args.lvlset)

  res = { }
  if (args.csv_table):
    print("Level,Invariants,TranslatedTo,Solved,Confirmed")

  for lvlName, lvl in lvls.iteritems():
    cppFile = lvl["path"][1]
    invgenCppFile = cppFile + ".invgen.preprocessed"

    if (not exists(invgenCppFile)):
      optionalManualModifiedFile = cppFile + ".invgen.manual.pretranslation";
      if (exists(optionalManualModifiedFile)):
        src = optionalManualModifiedFile
      else:
        src = cppFile;

      convertCppFileForInvGen(src, invgenCppFile);

    error("Running ", lvlName)

    mainRoutine = "main" if lvlName !="i-cegar1" else "cegar1"
    res[lvlName] = runInvGen(invgenCppFile, mainRoutine);

    solved, loopInvs, rawOutput = res[lvlName]
    conf_status = "n/a"

    if (solved == True):
      error("z3 invs: ", len(loopInvs), loopInvs)
      boogieInvs = map(parseInvGenInvariant, loopInvs);
      bbs = lvl["program"]
      loop = lvl["loop"]
      try:
        ((overfitted, overfitted2), (nonind, nonind2), sound, violations) =\
          tryAndVerifyLvl(lvl, set(boogieInvs), set(), args.time_limit, \
          addSPs=True, useSplitters=False, generalizeUserInvs = False)
        assert (len(overfitted2) == 0 and len(nonind2) == 0);
        if (len(violations) > 0):
          error("Supposedly sound inv: ", loopInvs)
          error("Results : ", overfitted, nonind, sound)
          error("Level ", lvlName, "false claimed to be sound!")
          error("Raw output: ", rawOutput)
          conf_status = False
        else:
          conf_status = True
      except Exception as e:
        if (e.message == "Unknown binary operator /"):
          conf_status = "unhandled division"
        else:
          raise e
    else:
      boogieInvs = []

    if (args.csv_table):
      print(lvlName, ",",\
            ";".join(map(str, loopInvs)), ",",\
            ";".join(map(str, boogieInvs)), ",",\
            res[lvlName][0], ",",\
            conf_status)
    else:
      print("Level", lvlName, "discovered:", loopInvs, "solved: ", solved, "confirmed?: ", conf_status)
