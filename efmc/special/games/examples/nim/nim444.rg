int: x[0,4], y[0,4], z[0,4]
init: x = 4 & y = 4 & z = 4
safe: (X < x & X >= 0 & Y = y & Z = z) | (Y < y & Y >= 0 & X = x & Z = z) | (Z < z & Z >= 0 & X = x & Y = y)
reach: (X < x & X >= 0 & Y = y & Z = z) | (Y < y & Y >= 0 & X = x & Z = z) | (Z < z & Z >= 0 & X = x & Y = y)
goal: x = 0 & y = 0 & z = 0