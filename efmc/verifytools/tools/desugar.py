#! /usr/bin/env python
import subprocess;
import os
import re
import sys
import traceback;
from os.path import dirname, abspath, realpath
from efmc.verifytools.boogie.bb import get_bbs
from efmc.verifytools.tools.boogie_loops import loops
from argparse import ArgumentParser


def error(msg):
    sys.stderr.write(msg)
    sys.exit(-1)


p = ArgumentParser(description="desugar file");
p.add_argument("inp_file", type=str, help="input file");
p.add_argument("out_file", type=str, help="output file");

MYDIR = dirname(abspath(realpath(__file__)))
BOOGIE_PATH = MYDIR + "/../env/third_party/boogie/Binaries/Boogie.exe"
#Z3_PATH = "E:\Gamification\inv-gen-game\env\third_party\z3\build\z3" 

def desugar(fname):
    output = subprocess.check_output(
            [BOOGIE_PATH, "/nologo", "/noinfer", "/traceverify", fname]);
    if (output.find("\r")>=0):
        lines = list(output.split("\r\n"))
    else:
        lines = list(output.split("\n"))
    start = 0;
    desugaredF = {}
    r = re.compile("implementation (?P<name>[^(]*)\(", re.MULTILINE)
    while True:
        try:
            code = "\n".join(lines[
                    lines.index("after desugaring sugared commands like procedure calls", start)+1:
                    lines.index("after conversion into a DAG", start)])
            name = r.findall(code)[0]
            desugaredF[name] = code;
            start = lines.index("after conversion into a DAG", start) + 1
        except ValueError:
            break;

    return desugaredF

if (__name__ == "__main__"):
  args = p.parse_args();

  print("Desugaring ", args.inp_file, " to ", args.out_file)
  res = desugar(args.inp_file);

  if (len(res) > 1):
      error("More than one function: " + ",".join(res.keys()));

  f = open(args.out_file, "w");
  f.write(res.values()[0]);
  f.close();
