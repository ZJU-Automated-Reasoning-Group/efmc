bool: x
int: z
init: x & z = 0
safe: (X <-> !x) & (Z = z) | (X <-> x) & (Z = z)
reach: !x & Z > z & (X <-> x) | Z = z & (X <-> !x)
goal: z = 5