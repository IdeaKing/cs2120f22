# Thomas Chia UJS4RC@VIRGINIA.EDU

"""Constraints for Sudoku:
- Each row must contain the numbers from 1 to 9 w/o repetitions
- Each column must contain the numbers from 1 to 9 w/o repetitions
- The digits can only occur once per block
- The sum of every single, row, column and nonet much equal 45
"""

from z3 import *


def sudoku_board(problem: list, solver: Solver, size: int = 9):
    """Creates the sudoku board, and adds the constraints to the solver.
    Returns:
        A solver.
    """
    # Create the board
    board = [[Int(f"cell_{r}_{c}") for c in range(size)] for r in range(size)]
    # Add the constriants to the solver
    # Each row and column can be a number from 1 to 9
    for column in range(size):
        for row in range(size):
            solver.add(board[row][column] >= 1) 
            solver.add(board[row][column] <= size)
        # Each row must have an unique value
        solver.add(Distinct(board[row]))
    # Each column must have an unique value
    for column in range(size):
            solver.add(Distinct([board[row][column] for row in range(size)]))
    # Each block must have an unique value
    for x in range(3):
        for y in range(3):
            solver.add(Distinct([board[x*3+i][y*3+j] for i in range(3) for j in range(3)]))
    # The sum of every single, row, column and nonet much equal 45
    # for column in range(size):
    #     for row in range(size):
    #         solver.add(Sum([board[row][column]]) == 45)
    solver = problem_to_list(
        problem=problem, 
        board=board, 
        solver=solver)
    return solver, board


def problem_to_list(problem: list, board: list, solver: Solver):
    """Converts a problem to a list of lists of integers."""
    for row in range(9):
        for column in range(9):
            number_val = problem[row][column]
            if number_val != ".":
                solver.add(board[row][column] == int(number_val))
    return solver


def display_results(model: Model, board: list):
    """Displays the results of the solver."""
    for row in range(9):
            print([f"{str(model.eval(board[row][column]))}" for column in range(9)])
    print()


def main(problem: list):
    """Given a sudoku list, create a solver and solve the problem.
    Args:
        problem: A list of lists of integers.
    """
    # Create the solver
    solver = Solver()
    # Create the board
    solver, board = sudoku_board(
        problem=problem,
        solver=solver)
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        display_results(model, board)
    else:
        print("No solution")


if __name__ == "__main__":
    # Add the problem here:
    problem = [
        "4..7.25..",
        "9...5....",
        ".214...98",
        "2....7...",
        ".6..2..4.",
        "...5....7",
        "83...615.",
        "....1...3",
        "..49.5..2"
    ]
    main(problem)