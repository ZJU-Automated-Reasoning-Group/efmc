real: x, y, c
init: x = 0.0 & y = 0.0 & c = 0.0
safe: x = 5.0 & y = 5.0 & X = -5.0 & Y = -5.0 & C = c + 1.0 | c < 20.0 & c >= 19.0 & X = x & Y = y & C = c | !(x = 5.0 & y = 5.0) & X = x & Y = y & C = c 
reach: C = c
goal: c = 100.0