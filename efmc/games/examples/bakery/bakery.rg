real: a[0.0,4.0],b[0.0,4.0],x[0.0,2.0],y[0.0,2.0]
init: a = 0.0 & b = 0.0 & x = 0.0 & y = 0.0
safe: A = a & Y = y & X = x & B = b
reach: ((a = 0.0 & A = 1.0 & Y = y | a = 1.0 & A = 2.0 & Y = x + 1.0 | (x = 0.0 | y <= x) & a = 2.0 & A = 3.0 & Y = y | !(x = 0.0 | y <= x) & a = 2.0 & A = 2.0 & Y = y | a = 3.0 & A = 4.0 & Y = y | a = 4.0 & A = 1.0 & Y = 0.0) & X = x & B = b) 
     | ((b = 0.0 & B = 1.0 & X = x | b = 1.0 & B = 2.0 & X = y + 1.0 | b = 2.0 & B = 3.0 & (y = 0.0 | x < y) & X = x | b = 2.0 & B = 2.0 & !(y = 0.0 | x < y) & X = x | b = 3.0 & B = 4.0 & X = x | b = 4.0 & B = 1.0 & X = 0.0) & Y = y & A = a)
goal: a = 3.0 & b = 3.0