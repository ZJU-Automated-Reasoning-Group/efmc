from tempfile import NamedTemporaryFile
from subprocess import call, check_output, STDOUT
from os.path import dirname, abspath, relpath
import os
from pydot import graph_from_dot_file
from efmc.verifytools.common.util import unique
from z3 import parse_smt2_string
import re

MYDIR = dirname(abspath(relpath(__file__)))

ICE_PATH = MYDIR + \
           "/../../../env/third_party/ice/Boogie/Binaries-full/"


def parseAbstractionFile(fname):
    lines = filter(lambda x: x != '',
                   map(lambda x: x.strip(), open(fname).read().split("\n")))
    decls = []
    invs = {}
    label_re = re.compile(
        "^(?P<n1>[0-9]*) \((?P<n2>[0-9,]*)\) \@(?P<n3>[0-9]*):$");
    var_re = re.compile("\|[a-zA-Z0-9]*::([a-zA-Z0-9_]*)\|")
    cur_lbl = None
    for l in lines:
        if l.startswith("(declare-fun"):
            decls.append(var_re.sub(r"\1", l));
        elif (label_re.match(l)):
            cur_lbl = label_re.match(l).groupdict()["n3"];
        else:
            assert (cur_lbl != None)
            full_str = "\n".join(decls + [var_re.sub(r"\1", l)])
            invs[cur_lbl] = invs.get(cur_lbl, []) + [parse_smt2_string(full_str)]
    return invs


def parseInvariantsFile(fname):
    lines = filter(lambda x: x != '',
                   map(lambda x: x.strip(), open(fname).read().split("\n")))
    label_re = re.compile("^[^ ]* [^ :]*:$")
    label_lines = [l for l in lines if label_re.match(l)]
    assert (len(label_lines) == 1)  # Single loop header so single invariant

    lines = [l for l in lines if not label_re.match(l)]
    var_re = re.compile("\|[a-zA-Z0-9]*::([a-zA-Z0-9_]*)\|")

    full_str = "\n".join([var_re.sub(r"\1", l) for l in lines])
    return parse_smt2_string(full_str);


def getLoopInvariants(outputDir):
    loopHeader = findLoopHeaderLabel(outputDir + "/cfa.dot")
    invs = parseAbstractionFile(outputDir + "/abstractions.txt")
    inv = parseInvariantsFile(outputDir + "/invariantPrecs.txt")
    return invs[loopHeader] + [inv]


def runICE(inpFile, timelimit=100):
    config = "predicateAnalysis-ImpactRefiner-ABEl.properties"
    nondetFunctions = ["unknown1", "unknown2", "unknown3", "unknown4", \
                       "unknown5", "random", "__VERIFIER_nondet_int", \
                       "__VERIFIER_nondet_uint"
                       ]
    args = [ICE_PATH + "Boogie.exe",
            "-nologo",
            "-timelimit", str(timelimit),
            "-noinfer",
            "-contractInfer",
            "-ice",
            "-printAssignment",
            "-trace",
            inpFile]
    raw = check_output(args, stderr=STDOUT);
    lines = raw.split("\n");
    lines = [x for x in lines
             if not (x.startswith("Running CPAchecker with") or
                     x.startswith("Using the following resource") or
                     x.startswith("CPAchecker 1.4-svcomp16c (OpenJDK") or
                     x.startswith("Using predicate analysis with") or
                     x.startswith("Using refinement for predicate analysis") or
                     x.startswith("Starting analysis ...") or
                     x.startswith("Stopping analysis ...") or
                     x.startswith("More details about the verification run") or
                     len(x.strip()) == 0)]
    verified = len([x for x in lines if "Verification result: TRUE." in x]) > 0

    headerLabel = findLoopHeaderLabel("output/cfa.dot")
    invs = getLoopInvariants("output/")
    return (verified, headerLabel, invs, "\n".join(lines))
