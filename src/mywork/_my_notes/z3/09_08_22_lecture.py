from z3 import * 


def shape_problem():
    solver = Solver()
    t, s, c = Ints('t s c')
    
    solver.add(t + s + c == 10)
    solver.add(c + s - t == 6)
    solver.add(c + t - s == 4)
    
    if solver.check() == sat:
        print(solver.model())


if __name__ == "__main__":
    shape_problem()