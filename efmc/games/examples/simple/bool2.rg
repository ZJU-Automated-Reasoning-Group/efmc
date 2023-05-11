bool: x, y
init: x & y
safe: (X <-> !x) & (Y <-> y) | (X <-> x) & (Y <-> !y)
reach: (X <-> !x) & (Y <-> !y) | (X <-> !x) & (Y <-> !y)
goal: !x & !y