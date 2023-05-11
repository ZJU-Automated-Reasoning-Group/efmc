int: x[0,3], y[0,3], z[0,3]
init: x = 3 & y = 3 & z = 3
safe: (X < x & X >= 0 & Y = y & Z = z) | (Y < y & Y >= 0 & X = x & Z = z) | (Z < z & Z >= 0 & X = x & Y = y)
reach: (X < x & X >= 0 & Y = y & Z = z) | (Y < y & Y >= 0 & X = x & Z = z) | (Z < z & Z >= 0 & X = x & Y = y)
goal: x = 0 & y = 0 & z = 0