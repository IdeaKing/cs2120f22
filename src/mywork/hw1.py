# Thomas Chia UJS4RC@VIRGINIA.EDU

""" Notes on Z3 (SAT):

1. Initialize the variables (Bools, Reals, Ints, etc...)
2. Define the disjunctions (Or, And, Not) and the formula (F)
3. Instantiate the Solver class and add the formula to the stack
4. SAT check: s.check()
5. Access the values in the assignments: s.model() and m.evaluate(F)

Solvers are Efficient algorithms to solve SAT.
SATs can solve general problems with constraints (Sudoku, n-queens, etc.)

Encodings:
Literals = model -> Values of literals (the answers to the problem)
Constraints = Problem has solution -> encoding has the solution

"""

from z3 import *
from itertools import combinations


def main():
    problem1()
    five_queens_problem()


def problem1():
    """ The formula of interest:
        F = (x or y or z) and (not x or not y) and (not y or not z)
        Determine if F is satisfiable.
    """
    # Creating the literals x, y, and z
    x, y, z = Bools("x y z")
    # Build the disjunctions in the formula
    # Basically each disjunction is a separate variable
    f1 = Or([x, y, z])
    f2 = Or([Not(x), Not(y)])
    f3 = Or([Not(y), Not(z)])
    # We use "And" to combine the disjunctions
    F = And([f1, f2, f3])
    # Instantiate the Solver class
    s = Solver()
    # A solver has a stack of assertions
    # We must add the assertions to the stack
    s.add(F)
    s.check()
    # To access the values in the assignments
    print(s.model()) # Gets the models


def five_queens_problem():
    """ 5-queens solver.
    Constraints:
    - 5x5 grid -> 25 booleans
    - Place 5 queens
    - No queens on the same row
    - No queens on the same column
    - No queens on the same diagonal  
    """
    def at_most_one(literals):
        c = []
        for pair in combinations(literals, 2):
            a, b = pair[0], pair[1]
            c += [Or(Not(a), Not(b))]
        return And(c)
    # Create all the literals for the board
    x = [[Bool("x_%i_ %i" % (i, j)) for j in range(5)] for i in range(5)]
    # Solver Instance
    s = Solver()
    # Add the constraints to the solver
    # Constraint: At least one queen per row
    for i in range(5):
        s.add(Or(x[i])) 
    # Constraint: At most one queen per column
    for i in range(5):
        col = []
        for j in range(5):
            col += [x[j][i]]
        s.add(at_most_one(col))
        s.add(at_most_one(x[i]))
    # Constraint: At most one queen per diagonal
    for i in range(4):
        diag_1 = []
        diag_2 = []
        diag_3 = []
        diag_4 = []
        for j in range(5 - i):
            diag_1 += [x[i+j][j]]
            diag_2 += [x[i+j][4-j]]
            diag_3 += [x[4-(i+j)][j]]
            diag_4 += [x[4-(i+j)][4-j]]
            
        s.add(at_most_one(diag_1))
        s.add(at_most_one(diag_2))
        s.add(at_most_one(diag_3))
        s.add(at_most_one(diag_4))
    # Print out the board
    if s.check() == sat:
        m = s.model()
        for i in range(5):
            line = ""
            for j in range(5):
                eval = m.evaluate(x[i][j])
                if eval:
                    line += "X "
                else:
                    line += ". "
            print(line)
    
    
if __name__ == "__main__":
    main() # :)