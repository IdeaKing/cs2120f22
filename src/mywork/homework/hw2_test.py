from z3 import *

# 1. Affirming the disjunct

x, y, z = Bools("x y z")

C1 = Implies(And(Or(x, y), x), Not(y))