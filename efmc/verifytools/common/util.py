import traceback
from functools import reduce
from itertools import chain, combinations
from sys import exc_info, stderr
from random import choice

def error(*args):
  if (len(args) > 0 and str(args[0]) and '%' in args[0]):
    fmt = args[0]
    rest = args[1:]
    if '\n' not in fmt:
        fmt += '\n'
    stderr.write(fmt % tuple(rest))
  else:
    stderr.write(" ".join(map(str, args)) + "\n")

def fatal(*args):
  error(*args)
  exit(-1)

def unique(iterable, msg=""):
  """ assert that iterable has one element and return it """
  l = list(iterable)
  assert len(l) == 1, msg
  return l[0]

def pp_exc(f):
    """ Wrap a function to catch, pretty print the exception and re-raise it.
    """
    def decorated(*args, **kwargs):
        try:
            return f(*args, **kwargs)
        except Exception:
            traceback.print_exception(*exc_info())
            raise
    return decorated

def powerset(s):
  """ Return the powerset of a set s """
  it = chain.from_iterable(combinations(s, l) for l in range(len(s) + 1))
  for subS in it:
    yield set(subS)

def average(vals):
    return sum(vals) / (1.0 * len(vals))

def split(pred, itr):
    """ Split a list based on a predicate function """
    yes,no = [], []
    for i in itr:
        if (pred(i)):
            yes.append(i);
        else:
            no.append(i);

    return (yes, no)

def nonempty(lst):
    """ Filter out the empty elements of a list (where empty is len(x) == 0)
    """
    return filter(lambda x: len(x) > 0, lst)

def nodups(s):
  return list(set(s))

def flattenSet(s):
  return reduce(lambda x,y: set(x).union(y), s, set([]))

def flattenList(s):
  return reduce(lambda x,y: x + y, s, [])

def randomToken(l):
  alphanum = "".join([chr(ord('a') + i) for i in range(26) ] +\
          [ str(i) for i in range(0,10)])
  return "".join([ choice(alphanum) for _ in range(l) ]);
