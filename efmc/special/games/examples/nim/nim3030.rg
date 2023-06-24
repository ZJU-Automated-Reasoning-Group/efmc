int: x, y
init: x = 30 & y = 30
safe: (X < x & X >= 0 & Y = y) | (Y < y  & Y >= 0 & X = x)
reach: (X < x & X >= 0 & Y = y) | (Y < y  & Y >= 0 & X = x)
goal: x = 0 & y = 0