bool: p, a
real: x[0.0,10.0], y[0.0,10.0], t[0.0,2.0]
init: !p & a & x = 0.0 & y = 0.0 & t = 0.0
safe: (P <-> p) & X = x & Y = y & (T = t - 1.0 & (A <-> a) | t <= 0.0 & T = 2.0)
reach: T = t & X <= x + 1.0 & X >= x - 1.0 & Y <= y + 1.0 & Y >= y - 1.0 & (!(X = 0.0 & Y = 10.0) -> (A <-> a)) & (a -> !(X = 10.0 & Y = 5.0)) & (!(X = 10.0 & Y = 5.0) -> (P <-> p))
goal: p