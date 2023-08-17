
def _get_var(c):
  return set([v for v, _ in c])

def _get_cubes_with_fewer_var(cubes, vset):
  # sort based on variable
  return [dict(cube) for cube in cubes if _get_var(cube).issubset(vset)]

def _get_cubes_with_more_var(cubes, vset):
  # sort based on variable
  return [dict(cube) for cube in cubes if _get_var(cube).issuperset(vset)]


def _get_unified_width(v): # bool 0, bv ...
  if v.get_type().is_bool_type():
    return 0
  assert (v.get_type().is_bv_type())
  return v.bv_width()
