real: a, e, p, x, y
init: x = y & y = 0.0 & a = 0.0 & e = 0.0 & p = 0.0
safe: (E <= e + 1.0 & E >= e - 1.0 & A = a & P = p & X = x & Y = y) | (a >= 500.0 & A = 0.0 & E = 0.0 & P = p + 1.0 & X = x & Y = y + 1.0)
reach: (a < 1000.0 & A <= a + 2.0 & A >= a - 2.0 & E = e & P = p & X = x & Y = y) | (a >= 1000.0 & A = 0.0 & E = 0.0 & P = p + 1.0 & X = x + 1.0 & Y = y)
goal: x > y & p <= 75.0