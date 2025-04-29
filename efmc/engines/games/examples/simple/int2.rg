int: x, y
init: x = 0 & y = 0
safe: X = x + 1 & Y = y | X = x & Y = y + 1
reach: X = x & Y = y + 1 | X = x & Y = y - 1
goal: x = 3 & y = 0