from efmc.verifytools.boogie.ast import parseExprAst, ast_or, ast_and
from efmc.verifytools.boogie.bb import get_bbs, ensureSingleExit, bbEntry
from efmc.verifytools.tools.boogie_loops import loops, get_loop_header_values
from efmc.verifytools.common.util import unique, powerset, average, error
from efmc.verifytools.boogie.analysis import livevars
from efmc.verifytools.boogie.eval import instantiateAndEval, evalPred, _to_dict, execute
from collections import OrderedDict
from functools import reduce
from os import listdir
from os.path import dirname, join, abspath, realpath
from itertools import product
from json import load, dumps
from random import randint
from vc_check import loopInvOverfittedCtrex

def _tryUnroll(loop, bbs, min_un, max_un, bad_envs, good_env):
    # Lets first try to find a terminating loop between min and max iterations
    term_vals = get_loop_header_values(loop, bbs, min_un, max_un,
                                       bad_envs, good_env, True)
    if (term_vals != []):
      return (term_vals, True)

    # Couldn't find a terminating loop between 0 and 6 iteration. Lets find
    # a loop that has at LEAST min iterations
    term_vals = get_loop_header_values(loop, bbs, min_un, max_un,
                                       bad_envs, good_env, False)
    return (term_vals, False)

def varproduct(vargens):
  # Take var: gen and generate all var assignments (smallest first), i.e.
  # "A": count(), "B": count() yields
  #   (A, B) = (0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0), ...
  if len(vargens.items()) == 0:
    yield {}
  else:
    vars_, gens = zip(*vargens.items())
    for vals in product(*gens):
      yield dict(zip(vars_, vals))

def getEnsamble(loop, bbs, exec_limit, tryFind=100, distr=lambda: randint(0,5),
        include_bbhit=False, vargens=None):
    loopHdr = loop.loop_paths[0][0]
    traceVs = list(livevars(bbs)[loopHdr])
    if vargens is None:
      def candidatef():
        while True:
          yield {v: distr() for v in traceVs}
      candidategen = candidatef()
    else:
      candidategen = varproduct(vargens)
    tried = set();
    #TODO: Not a smart way for generating random start values. Fix.
    s = 0
    print("Trying to find ", tryFind, " traces of length up to ", exec_limit)
    while s < tryFind:
        candidate = next(candidategen)
        hashable = tuple(candidate[v] for v in traceVs)
        if hashable in tried:
          continue
        tried.add(hashable)

        found = False
        trace = execute(candidate, bbEntry(bbs), bbs, exec_limit)
        for _, _, _, ssap, vals in trace:
          vals = [ envs[0] for (bb, envs) in vals if bb == loopHdr ]
          if include_bbhit:
            bbhit = set(bbname for bbname, _ in ssap)
            yield (vals, bbhit)
          else:
            yield vals
          found = True;
          s += 1
          if (s >= tryFind):
            break;

        if (not found):
            s += 1;

def getInitialData(loop, bbs, nunrolls, invs, invVars = None, invConsts = None):
    if (invConsts == None):
        invConsts = ["_sc_a", "_sc_b", "_sc_c"]
    trace_enasmble = list(getEnsamble(loop, bbs, nunrolls, 1))
    vals, _ = _tryUnroll(loop, bbs, 0, nunrolls, None, None)
    if (vals):
        trace_enasmble.append(vals)
    
    traceVs = list(livevars(bbs)[loop.loop_paths[0][0]])
    trace_enasmble = [ [ { varName: env[varName] for varName in traceVs }
                       for env in tr ]
                     for tr in trace_enasmble ]

    if (invVars == None):
        invVars = traceVs

    invs_lst = [ reduce(lambda x,y: x+y,
                        [ instantiateAndEval(inv, trace, invVars, invConsts)
                            for inv in invs ],
                        [])
                 for trace in trace_enasmble if len(trace) > 0 ]

    tmp_lst = [ (len(invs), invs, tr)
                for (invs, tr) in zip(invs_lst, trace_enasmble) ]

    tmp_lst.sort(key=lambda t:  t[0]);
    return (tmp_lst[0][2], False)


def findNegatingTrace(loop, bbs, nunrolls, invs, invVrs = None):
    vals, terminates = _tryUnroll(loop, bbs, 0, nunrolls, None, None)
    traceVs = list(livevars(bbs)[loop.loop_paths[0][0]])
    vals = [ { x : env[x] for x in traceVs } for env in vals ]
    hold_for_data = []

    if (invVrs == None):
        invVrs = traceVs

    def diversity(vals):
        lsts = [ [ vals[i][k] for i in range(len(vals)) ]
                 for k in vals[0].keys() ]
        return average([len(set(lst)) for lst in lsts])
        #return average([len(set(lst)) / 1.0 * len(lst) for lst in lsts])

    for inv in invs:
        hold_for_data.extend(instantiateAndEval(inv, vals, invVrs,
                                                ["_sc_a", "_sc_b", "_sc_c"]))

    print("The following invariants hold for initial trace: ", hold_for_data)
    hold_for_data = list(set(hold_for_data))
    print("The following remain after clearing duplicates: ", hold_for_data)
    res = [ ]
    no_ctrex = set([])
    for s in powerset(hold_for_data):
        if (s.issubset(no_ctrex)):
            continue
        #print "Looking for ctrex for: ", s, " with no_ctrex: ", no_ctrex
        inv = ast_or(s)
        ctrexs = loopInvOverfittedCtrex(loop, inv, bbs)
        if (len(ctrexs) > 0):
            for ctrex in ctrexs:
              trace, terminates = \
                      _tryUnroll(loop, bbs, 0, nunrolls, None, ctrex)
              if (len(trace) > 0):
                  print("Ctrexample for ", inv, " is ", trace)
                  res.append((diversity(trace), len(s), list(s),
                              ctrex, (trace, terminates)))
        else:
            no_ctrex = no_ctrex.union(s)

    res.sort(key=lambda x:  x[0]);
    if (len(res) > 0):
        return res[-1][4]
    else:
        return (None, False)

def readTrace(fname):
    trace = open(fname, "r").read();
    lines = filter(lambda x: len(x) != 0,
                   map(lambda x:   x.strip(), trace.split('\n')))
    vs = filter(lambda x:   len(x) != 0, lines[0].split(' '))
    header_vals = [ ]
    for l in lines[1:]:
        if (l[0] == '#'):
            continue;

        env = { }
        for (var,val) in zip(vs, filter(lambda x: len(x) != 0, l.split(' '))):
            env[var] = val
        header_vals.append(env);
    return (vs, header_vals)

def writeTrace(fname, header_vals):
    f = open(fname, "w");

    if (len(header_vals) != 0):
      vs = header_vals[0].keys();
      f.write(" ".join(vs) + "\n");
      for env in header_vals:
        f.write(" ".join([str(env[v]) for v in vs]) + "\n")

    f.close();

#TODO: Remove multiround. Its crud.
def loadBoogieFile(fname, multiround):
    bbs = get_bbs(fname)
    ensureSingleExit(bbs);
    loop = unique(loops(bbs),
                  "Cannot handle program with multiple loops:" + fname)

    # The variables to trace are all live variables at the loop header
    vs = list(livevars(bbs)[loop.loop_paths[0][0]])

    # Make sure variable names are different modulo case
    assert len(vs) == len(set([var.lower() for var in vs]))

    # See if there is a .trace or a .hint file
    hint = None
    header_vals = None;
    terminates = False;
    try:
        (vs, header_vals) = readTrace(fname[:-4] + '.trace')
        hint = load(open(fname[:-4] + '.hint'))
    except Exception: #TODO (Dimo) IOError here instead?
        pass

    if (not header_vals):
        header_vals, terminates = _tryUnroll(loop, bbs, 0, 4, None, None)
        # Assume we have no tests with dead loops
        assert(header_vals != [])
        invTemplates = ["_sv_x<_sv_y", "_sv_x<=_sv_y", "_sv_x==_sc_c", \
                        "_sv_x==_sv_y", "_sv_x==0", "_sv_x<0"]
        invTemplates = [ parseExprAst(inv) for inv in invTemplates]

        new_header_vals, new_terminates = \
                getInitialData(loop, bbs, 4, invTemplates, [ "_sv_x", "_sv_y" ])

        if (new_header_vals != None):
            header_vals = new_header_vals
            terminates = new_terminates
            writeTrace(fname[:-4] + ".trace", new_header_vals);

    return { 'variables': vs,
             'data': [ [[ str(row[v]) for v in vs  ] for row in header_vals],
                       [],
                       [] ],
             'exploration_state' : [ ( [str(header_vals[0][v]) for v in vs],
                                       len(header_vals),
                                       terminates ) ],
             'hint': hint,
             'goal' : { "verify" : True },
             'support_pos_ex' : True,
             'support_neg_ex' : True,
             'support_ind_ex' : True,
             'multiround'     : multiround,
             'program' : bbs,
             'loop' : loop
    }

def loadBoogies(dirN, multiround = False):
    return { name[:-4] : loadBoogieFile(dirN + '/' + name, multiround)
             for name in listdir(dirN) if name.endswith('.bpl') }

def readTraceOnlyLvl(fname):
    rows = []
    first = True
    for l in open(fname):
        l = l.strip();
        if (l == ''):
            continue
        row = {}
        for (n,v) in [x.split('=') for x in l.split(' ')]:
            row[n] = v

        if (first):
          vs = [x.split('=')[0] for x in l.split(' ')]
          first = False;
        rows.append(row)

    hint = None
    goal = None
    try:
        goal = load(open(fname[:-4] + '.goal'))
        hint = open(fname[:-4] + '.hint').read()
    except Exception:
        pass

    return { 'variables': vs,
             'data': [[[ row.get(n, None) for n in vs  ]  for row in rows ],
                      [],
                      []],
             'hint': hint,
             'goal' : goal,
             'support_pos_ex' : False,
             'support_neg_ex' : False,
             'support_ind_ex' : False,
             'multiround'     : False,
    }

def loadTraces(dirN):
    return { name[:-4] : readTraceOnlyLvl(dirN + '/' + name)
             for name in listdir(dirN) if name.endswith('.out') }

def loadBoogieLvlSet(lvlSetFile):
    # Small helper funct to make sure we didn't
    # accidentally give two levels the same name
    def assertUniqueKeys(kvs):
      keys = [x[0] for x in kvs]
      assert (len(set(keys)) == len(keys))
      return dict(kvs)

    lvlSet = load(open(lvlSetFile, "r"), object_pairs_hook=assertUniqueKeys)
    lvlSetDir = dirname(abspath(realpath(lvlSetFile)))
    error("Loading level set " + lvlSet["name"] + " from " + lvlSetFile);
    lvls = OrderedDict()
    for t in lvlSet["levels"]:
        lvlName = t[0]
        lvlPath = t[1]

        for i in range(len(lvlPath)):
          lvlPath[i] = join(lvlSetDir, lvlPath[i])
            
        error("Loading level: ", lvlPath[0])
        lvl = loadBoogieFile(lvlPath[0], False)
        lvl["path"] = lvlPath

        if (len(t) > 2):
          splitterPreds = [ parseExprAst(exp) for exp in t[2] ]
          splitterPred = ast_and(splitterPreds)
          remainderInv = parseExprAst(t[3])

          lvl['data'][0] = filter(
            lambda row: evalPred(splitterPred, _to_dict(lvl['variables'], row)),
            lvl['data'][0]);

          if (len(lvl['data'][0]) == 0):
            error("SKIPPING : ", lvlName, " due to no filtered rows.")
            continue

          lvl['partialInv'] = remainderInv
          lvl['splitterPreds'] = splitterPreds

        lvls[lvlName] = lvl;

    return (lvlSet["name"], lvls)
