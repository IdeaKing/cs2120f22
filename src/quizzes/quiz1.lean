/-
CS2120 Fall 2022 Sullivan. Quiz #1. Edit your answers into
this file using VSCode. Save the file to your *local* hard 
drive (File > Save As > local > ...). Submit it to the Quiz1
assignment on Collab.
-/

/-
#1: For each of the following questions give a yes/no answer 
and then a very brief explanation why that answer is correct.
To explain why your answer is correct, name the specific rule
of inference that tells you it's correct, or explain that 
there is no such valid inference rule.
-/

/-
#1A

If a ball, b, is round *and* b is also red, is b red?

A: yes/no: 
  yes

B: Why? 
  And elimination right rule; if b is an arbitrary but specific ball, 
  and b is round and red, b must be red too. 

  ∀ (b: Prop), isRound b ∧ isRed b -> isRed b


#1B

If flowers make you happy and chocolates make you happy,
and I give you flowers *or* I give you chocolates, will
you be happy?

A: yes/no: 
  yes

B: Why? 
  Or elimination rule. Either the flowers or the chocolates 
  will make you happy, thus, recieving either the flowers or the 
  chocolates will make you happy. Futhermore, the "and" in the 
  question is not inclusive, where it is required for both flowers
  and chocolates to make one happy.

  ∀ (f, c, h: Prop), (f ∨ c) → (f → h) → (c → h) → h


#1C: If giraffes are just zebras in disguise, then the 
moon is made of green cheese?

A. yes/no: 
  yes

B. Why? 
  False elimination, if we assume that the false proposition is true, 
  then any other proposition is true. Eplicitly, if giraffes are 
  zebras in stripes is true, than anything can be true, because from
  a false proposition, anything goes.

∀ (g, m : Prop), g → m


#1D. If x = y implies that 0 = 1, then is it true that
x ≠ y?

A. yes/no: 
  no

B. Why? 
  There is no such rule valid inference rule. If we assume x = y to be true
  and 0 = 1, 0 does not equal 1 so it is false, and true can not imply false,
  thus this is not possible.



#1E. If every zebra has stripes and Zoe is a Zebra then
Zoe has stripes.

A. yes/no: 
  yes

B. Why?
  Implication introduction rule. If all zebras have stripes, and 
  Zoe is an arbitrary but specific zebra, zoe must have stripes
  because zoe is a zebra. 




#1F. If Z could be *any* Zebra and Z has stripes, then 
*every* Zebra has stripes.

A. Yes/no: 
  yes

B: Why?
  [Forgot the rule]. If an arbitrary but specific zebra Z has stripes,
  then it must be the case that every and all zebras have stripes.


#1G. If whenever the wind blows, the leaves move, and 
the leaves are moving, then the wind is blowing.

A. yes/no: 
  no

B. Why? 
  There is no such valid inference rule. If the wind blows is 
  true implies the leaves move is true, but it the leaves move is true,
  it doesn't necessarily imply that the wind is blowing.


#1H: If Gina is nice *or* Gina is tall, and Gina is nice,
then Gina is not tall. (The "or" here is understood to be
the or of predicate logic.)

A. yes/no: 
  no


B. Why?
  There is no such valid inference rule, gina could be nice and tall
  but it would not imply that she is not tall on the premise that she
  is nice.

  ∀ (g : Prop), (isNice g ∨ isTall g ) ∧ isNice g → ¬isTall g
-/



/- 
#2

Consider the following formula/proposition in propositional
logic: X ∨ ¬Y.

#2A: Is is satisfiable? If so, give a model (a binding of 
the variables to values that makes the expressions true).

  It is satisfiable. If X is true and Y is false, it would be True.


#2B: Is it valid? Explain your answer. 

  It is not valid, because there are cases where it isn't satisfiable;
  for instance, when X is false and is true.


-/


/-
#3: 

Express the following propositions in predicate logic, by
filling in the blank after the #check command.

If P and Q are arbitrary (any) propositions, then if (P is 
true if and only if Q is true) then if P is true then Q is 
true.
-/

#check ∀ (p, q : Prop), p ↔ q → p → q 


/-
#4 Translate the following expressions into English.
The #check commands are just Lean commands and can
be ignored here. 
-/


-- A
#check ∀ (n m : ℕ), n < m → m - n > 0

/-
Answer: 
  If n and m are any natural numbers, if n is 
  less than m is true, then m minus n will always
  be greater than 0.
-/

-- B

#check ∃ (n : ℕ), ∀ (m : nat), m >= n

/-
Answer:
  There exists some natural number n and for all natural number m
  where m is greater than or equal to n is true.
-/


-- C

variables (isEven: ℕ → Prop) (isOdd: ℕ → Prop)
#check ∀ (n : ℕ), isEven n ∨ isOdd n

/-
Answer:
  For all propositions n, n is even or n is odd is true.
-/


-- D

#check ∀ (P : Prop), P ∨ ¬P

/-
Answer: 
  For all propositions P, P or not P is true.
-/


-- E

#check ∀ (P : Prop), ¬(P ∧ ¬P)

/-
Answer:
  For all propositions P, P or not P is true.
-/


/-
#5 Extra Credit

Next we define contagion as a proof of a slightly long
proposition. Everything before the comma introduces new
terms, which are then used after the comma to state the
main content of the proposition. 

Using the names we've given to the variables to infer
real-world meanings, state what the logic means in plain
natural English. Please don't just give a verbatim reading
of the formal logic. 
-/

variable contagion : 
  ∀ (Animal : Type) 
  (hasVirus : Animal → Prop) 
  (a1 a2 : Animal) 
  (hasVirus : Animal → Prop)
  (closeContact : Animal → Animal → Prop), 
  hasVirus a1 → closeContact a1 a2 → hasVirus a2

/- 
Answer:
  If it is true that an animal "a1" has a virus, and then 
  it is true that it is in close contact with another animal "a2", 
  then "a2" it is true that a2 has a virus.

-/

