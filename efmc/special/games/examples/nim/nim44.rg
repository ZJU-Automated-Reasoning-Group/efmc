int: x, y
init: x = 4 & y = 4
safe: (X < x & X >= 0 & Y = y) | (Y < y  & Y >= 0 & X = x)
reach: (X < x & X >= 0 & Y = y) | (Y < y  & Y >= 0 & X = x)
goal: x = 0 & y = 0