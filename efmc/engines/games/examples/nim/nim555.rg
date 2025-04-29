int: x[0,5], y[0,5], z[0,5]
init: x = 5 & y = 5 & z = 5
safe: (X < x & X >= 0 & Y = y & Z = z) | (Y < y & Y >= 0 & X = x & Z = z) | (Z < z & Z >= 0 & X = x & Y = y)
reach: (X < x & X >= 0 & Y = y & Z = z) | (Y < y & Y >= 0 & X = x & Z = z) | (Z < z & Z >= 0 & X = x & Y = y)
goal: x = 0 & y = 0 & z = 0