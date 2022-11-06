-- set theory

-- from predicates we will build up sets
-- define a set as a predicate
-- every object satisfy the set is in the set
-- every object not satisfy the set is not in the set

/-
Set notation



-/

def isEven (n : ℕ) : Prop := n % 2 = 0


def evens : set ℕ := {n : ℕ | isEven n}

-- some times can leave some stuff out

def evens' := {n : ℕ | isEven n}

