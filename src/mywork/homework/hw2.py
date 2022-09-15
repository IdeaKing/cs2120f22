# Thomas Chia, UJS4RC

from z3 import *


def main():
    def is_valid(proposition):
        """
        Check if a proposition is valid
        """
        solver = Solver()
        solver.add(Not(proposition))
        return solver.check() == unsat


    def disjunct():
        """
        1. (X or Y) and X entails Y.
        If X or Y is true then X entails not Y.
        Not a valid rule of reasoning.
        """
        x, y = Bools("x y")
        return Implies(And(Or(x, y), x), Not(y))


    def and_introduction():
        """
        2. (X and Y entails X and Y).
        If X and Y are true then X and Y are true.
        A valid rule of reasoning.
        """
        x, y = Bools("x y")
        return Implies(And(x, y), And(x, y))


    def and_elimination_left():
        """
        3. (X and Y entails X).
        If X and Y are true then X is true.
        A valid rule of reasoning.
        """
        x, y = Bools("x y")
        return Implies(And(x, y), x)


    def and_elimination_right():
        """
        4. (X and Y entails Y).
        If X and Y are true, then Y is true.
        A valid rule of reasoning.
        """
        x, y = Bools("x y")
        return Implies(And(x, y), y)


    def negation_elimination():
        """
        5. (Not Not X entails Y)
        If X is not not true, then Y is true.
        Not a valid rule of reasoning.
        """
        x, y = Bools("x y")
        return Implies(Not(Not(x)), x)


    def no_contradiction():
        """
        6. Not(X and Not X)
        It is not possible to have X and Not X be True
        Valid.
        """
        x, y = Bools("x y")
        return Not(And(x, Not(x)))


    def or_introduction_left():
        """
        7. X entails X or Y
        If X is true, then X or Y is True
        Valid.
        """
        x, y = Bools("x y")
        return Implies(x, Or(x, y))



    def or_introduction_right():
        """
        8. Y entails X or Y
        If Y is true, then X or Y is True
        Valid.
        """
        x, y = Bools("x y")
        return Implies(y, Or(x, y))


    def denying_the_antecedent():
        """
        9. X implies Y, Not X entails Not Y
        If X is True, then Y is True and if Not X is True, then Not Y is True
        Not Valid.
        """
        x, y = Bools("x y")
        return And(Implies(x, y), Implies(Not(x), Not(y)))


    def iff_introduction():
        """
        10. X implies Y, Y implies X entails X iff Y
        If X is true, Then Y is true, and if Y is true, then X is true if and only if Y is true
        Valid.
        """
        x, y = Bools("x y")
        return Implies(And(Implies(x, y), Implies(y, x)), x == y)


    def iff_elimination_left():
        """
        11. X iff Y entails X implies Y
        if X is True if and only if Y is true, then x is true if y is true.
        Valid.
        """
        x, y = Bools("x y")
        return Implies(x == y, Implies(x, y))


    def iff_elimination_right():
        """
        12. X iff Y entails Y implies X
        if X is True if and only if Y is true, then Y is true if X is true.
        Valid.
        """
        x, y = Bools("x y")
        return Implies(x == y, Implies(y, x))


    def or_elimination():
        """
        13. X or Y, X implies Z, Y implies Z entails Z
        If X is True or Y is True and if X is True then Z is True then if Y is True, then z is true 
        Not valid
        """
        x, y, z = Bools("x y z")
        return And(And(Or(x, y), Implies(x, z)), Implies(Implies(y, z), z))


    def affirmation_the_conclusion():
        """
        14. X implies Y, Y entails X
        If X is True, Y is True and if Y is True then X is True
        Not Valid
        """
        x, y = Bools("x y")
        return And(Implies(x, y), Implies(y, x))


    def arrow_elimination():
        """
        15. X implies Y, X entails Y
        If X is True, then Y is True, and if X is True, then Y is True
        Valid
        """
        x, y = Bools("x y")
        return And(Implies(x, y), Implies(x, y))


    def transitivity_of_arrow():
        """
        16. X implies Y, Y implies Z entails X implies Z
        If X is True, then Y is True, and if Y is True then Z is True, if that is True, then X is True, if that is True, then is Z is True
        Not Valid
        """
        x, y, z = Bools("x y z")
        return And(Implies(x, y), Implies(y, Implies(z, Implies(x, z))))


    def converse():
        """
        17. X implies Y entails Y implies X
        If X is true then y is true, if y is true, then y is true, then x is true
        Valid
        """
        x, y = Bools("x y")
        return Implies(x, Implies(y, Implies(y, x)))


    def contrapositive():
        """
        18. X implies Y enatils not Y implies X
        If X is true then y is true, if y is true, then not y is true, then not x is true
        Valid
        """
        x, y = Bools("x y")
        return Implies(x, Implies(y, Implies(Not(y), Not(x))))


    def demorgan_1():
        """
        19. Not(X or Y) Biconditional NotX and NotY
        Not X or Y is equal to Not X and Not Y
        True
        """
        x, y = Bools("x y")
        return (Not(Or(x, y)) == And(Not(x), Not(y)))


    def demorgan_2():
        """
        20. Not(X and Y) Biconditional NotX or NotY
        Not X and Y is equal to Not X or Not Y
        True
        """
        x, y = Bools("x y")
        return (Not(And(x, y)) == Or(Not(x), Not(y)))        


    inference_rules = [
        disjunct(), 
        and_introduction(), 
        and_elimination_left(), 
        and_elimination_right(),
        negation_elimination(),
        no_contradiction(),
        or_introduction_left(),
        or_introduction_right(),
        denying_the_antecedent(),
        iff_introduction(),
        iff_elimination_left(),
        iff_elimination_right(),
        or_elimination(),
        affirmation_the_conclusion(),
        arrow_elimination(),
        transitivity_of_arrow(),
        converse(),
        contrapositive(),
        demorgan_1(),
        demorgan_2()]
    
    for i, rule in enumerate(inference_rules):
        print(f"{i+1} is: ", is_valid(rule))


if __name__ == "__main__":
    main()