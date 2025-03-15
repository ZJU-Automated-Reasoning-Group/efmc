int: x[0,3], y[0,5], z[0,6]
init: x = 3 & y = 5 & z = 6
safe: (X < x & X >= 0 & Y = y & Z = z) | (Y < y & Y >= 0 & X = x & Z = z) | (Z < z & Z >= 0 & X = x & Y = y)
reach: (X < x & X >= 0 & Y = y & Z = z) | (Y < y & Y >= 0 & X = x & Z = z) | (Z < z & Z >= 0 & X = x & Y = y)
goal: x = 0 & y = 0 & z = 0