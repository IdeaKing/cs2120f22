from z3 import *

x, y = Reals("x y")
print(solve(x**2 + y**2 > 3, x**3 + y < 5))
