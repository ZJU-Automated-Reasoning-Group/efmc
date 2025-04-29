int: x[0,2], y[0,2], z[0,2], v[0,2]
init: x = 2 & y = 2 & z = 2 & v = 2
safe: (X < x & X >= 0 & Y = y & Z = z & V = v) | (Y < y & Y >= 0 & X = x & Z = z & V = v) | (Z < z & Z >= 0 & X = x & Y = y & V = v) | (V < v & V >= 0 & X = x & Y = y & Z = z)
reach: (X < x & X >= 0 & Y = y & Z = z & V = v) | (Y < y & Y >= 0 & X = x & Z = z & V = v) | (Z < z & Z >= 0 & X = x & Y = y & V = v) | (V < v & V >= 0 & X = x & Y = y & Z = z)
goal: x = 0 & y = 0 & z = 0 & v = 0