real: a, b
init: a = 0.0 & b = 3.0
safe: A = a & B >= b & B <= b + 2.0
reach: A >= a & A <= a + 2.0 & B = b
goal: a = b