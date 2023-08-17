bool: p, a
real: x, y
init: !p & a & x = 0.0 & y = 0.0
safe: (P <-> p) & X = x & Y = y
reach: X <= x + 1.0 & X >= x - 1.0 & Y <= y + 1.0 & Y >= y - 1.0 & (!(X = 0.0 & Y = 40.0) -> (A <-> a)) & (a -> !(X = 40.0 & Y = 20.0)) & (!(X = 40.0 & Y = 20.0) -> (P <-> p))
goal: p