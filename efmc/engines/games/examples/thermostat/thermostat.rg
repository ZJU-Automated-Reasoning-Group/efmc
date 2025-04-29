bool: o
real: c
init: !o & 20.8 <= c & c <= 23.5
safe: C = c
reach: (O <-> o) & (o & (C = c + 1.0 - (0.1 * (c - 19.0))) | !o & (C = c - (0.1 * (c - 19.0))))
goal: c < 20.0 | c > 25.0