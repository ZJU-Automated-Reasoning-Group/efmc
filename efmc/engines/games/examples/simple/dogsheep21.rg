int: x[0,5], y[0,5], d[0,20]
init: x = 2 & y = 2 & d = 0
reach: (X >= (x - 1)) & (X <= (x + 1)) & (Y >= (y - 1)) & (Y <= (y + 1)) & D = d
safe: (D >= (d - 2)) & (D <= (d + 2)) & X = x & Y = y
goal: x = 5 & y >= 2 & y <= 3 & ((d < 7) | (d > 8))
