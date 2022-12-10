import data.set
import logic.relation

/- ****** -/
/-   #1   -/
/- ****** -/

/-
A [5 points].

Give a formal definition of the proposition
that for every natural number, n, there's a
natural number, m, that's one more than n.
Replace the _ placeholder with your answer.
We will call your proposition prop1.
-/

def prop1 : Prop := 
  ∀ n : ℕ, ∃ m : ℕ, m = n + 1

/-
B [5 points].

Give a formal proof of this proposition. Include
a brief one line comment just before each line in 
your proof script explaining in English what it
does.
-/

example : prop1 :=
begin
unfold prop1, 
-- assume the arbitrary number n
assume n, 
-- there must be some number m which satisfies the constraint
apply exists.intro (n + 1),
-- The number m is n + 1 satisfies the constraint
apply eq.refl (n + 1),
end


/- #C [5 points]. Write a brief English language
proof of prop1.

Answer: Assume n is arbitrary. We're to show that 
there's a one larger number. The number, n + 1,
satisfies the constraint.  QED.
-/



/- ****** -/
/-   #2   -/
/- ****** -/

/-
We start by defining two "enumerated" data types, 
each with three values. We'll call them "lets" and
"nums," short for letters and numbers. The letters
are A, B, and C; and the numberrs are one, two, and
three.
-/

inductive lets : Type
| A
| B
| C

inductive nums : Type
| one
| two
| three

open lets nums


/- #A [5 points]

Define a function, l2n_ni (short for "letters to
numbers, not injective") using "by cases" syntax,
where l2n_ni is not injective. We don't care what
non-injective function you define, as long as it
is not injective. In a brief comment afterwards,
explain what makes it not injective.
-/

def l2n_ni : lets → nums
-- add rules here
| A := one
| B := one
| C := one


-- Answer (what makes it non-injective?):

  --**The function is not injective because it is many-to-one.**

/- #B [5 points]

Define a function, l2n_s (short for "letters to
numbers, surjective") using "by cases" syntax,
where l2n_s is surjective. We don't care what
surjective function you define. 
-/

def l2n_s : lets → nums
-- add rules here
| A := one
| B := two
| C := three

/- #C [5 points] 

Write a brief English-language proof showing that
your function is surjective. You must cite what it
means to be surjective (be mathematically precise).
Hint: You'll have to assume you're given any letter
as input. What you do with that arbitrary value to
complete the proof is the question to answer. Once
you have that, the rest is pretty straightforward.

Answer: 
  Assume that we are given an arbitrary letter A, B, or C.
  We must show that there every element of the output set is
  has a corresponding element in the input set since the
  function is surjective. 

  When given the arbitrary letter A, the function returns the
  number one. When given the arbitrary letter B, the function
  returns the number two. When given the arbitrary letter C,
  the function returns the number three.

  Since every element of the output set has a corresponding
  element in the input set, the function is surjective.
-/

/- # EXTRA CREDIT [5 points] 

Prove formally that l2n_s is surjective.
-/
open function

lemma l2n_s_surjective: surjective l2n_s :=
begin
-- Answer here
  unfold surjective,
  assume b,
  cases b,

  apply exists.intro A,
  unfold l2n_s,
  
  apply exists.intro B,
  unfold l2n_s,

  apply exists.intro C,
  unfold l2n_s,
end



/- ****** -/
/-   #3   -/
/- ****** -/


/- #A [ 5 points] 

Write a formal definition of the predicate,
"is_even," taking a single natural number, n,
and reducing to the proposition that n mod 2
is 0. When you have it right, the first test
should pass, the second, fail, the third pass,
etc. 
-/

-- Answer

def is_even : ℕ → Prop
| n := n % 2 = 0
-- or equivalent

-- tests
example : is_even 0 := rfl    -- even
example : is_even 1 := rfl    -- not even
example : is_even 2 := rfl    -- even
example : is_even 3 := rfl    -- not even
example : is_even 4 := rfl    -- even
example : is_even 5 := rfl    -- not even


/- #B [5 points]

Next, use set builder (comprehension) notation
to define the set of all even numbers, using
is_even as a "membership" predicate.
-/

def evens : set ℕ := 
  { n | is_even n}


/-
The next few problems use the following 
set.
-/

def under5 : set ℕ := {0, 1, 2, 3, 4, 5}

/- #C [5 points]

Prove: 2 ∈ evens ∩ under5. Hint: remember
wjat ∩ means logically, then use the right
logical inference rule. If you can't give
a formal proof, give a precise English
language proof instead, being precise
about the reasoning steps.
-/

example : 2 ∈ evens ∩ under5 :=
begin
  split,
  unfold evens,
  unfold is_even,
  simp,
  unfold under5,
  simp,
end 

/- D [5 points]

Consider the set, justA = { A }, of 
"lets" (letters) as (defined above). 
-/

def just_A : set lets := { A } 

/-
Prove that (the letter) C is in 
just_Aᶜ, the complement of just_A. 
If you have problems getting Lean to
check your proof, you may give an 
English language version, instead,
but be sure to state *exactly* what 
(C ∈ just_Aᶜ) means and each reasoning 
step in your informal proof.

-/

example : C ∈ just_Aᶜ := 
begin
-- Answer here
  unfold just_A,
  assume h,
  cases h,
end

/-
Proof: 
-/


/- #E [5 points]

How many subsets are there of 
each of the following sets? You can
give an approximate answer on #4. 
Hint on 5: Recall that 𝒫 S means
the powerset of a set, S. So on
question 5, we are asking how many
subsets are there of the powerset 
of {0,1,2}.


                          Answers
1. {}                     -- 1
2. {0,1,2}                -- 8
3. {0,1,2,3,4,5,6,7,8,9}  -- 1024
4. { n | 0 ≤ n ∧ n < 30}  -- 2^30 + 1 = 1073741825
5. 𝒫 {0,1,2}              -- 9
-/



/- ****** -/
/-   #4   -/
/- ****** -/


/- A [5 points]

Define a function, prod_to: ℕ → ℕ, that,
when applied to a given n returns: 1 if n
is zero; and otherwise (if n = succ n' for 
some n') the product of n and prod_to n'. 
You likely have it right when the tests all
pass.
-/

def prod_to : ℕ → ℕ 
| nat.zero := 1
| (nat.succ n') := nat.succ n' * prod_to n'

example : prod_to 0 = 1 := rfl
example : prod_to 1 = 1 := rfl
example : prod_to 2 = 2 := rfl
example : prod_to 3 = 6 := rfl
example : prod_to 4 = 24 := rfl


/- #B [5 points]

What is the common name of this function?

Answer: 
  **Geometric function.**

-/

--**4C is deleted.**--

/- #D [5 points]

This question tests your understanding of
the induction axiom for natural numbers.

You've learned that there are 2^n possible
"interpretations" of n propositional (i.e.,
Boolean) variables. Now *prove* that this 
is true. We'll help a bit. You fill in the
missing parts. 

1. The property, P, of n, we want to prove 
is that "the number of interpretations of 
a collection of n Boolean variables is 2^n." 

2. What we then want to prove is ∀ n, P n.  

3. What specific proposition do we want
to prove as the "base case" in a proof by
induction? Be mathematically precise.

Answer: 
  **The base case is: P n → P 0 (where n = 0).**

4. What specific proposition do we want to
prove as the "inductive case" in a proof by
induction? Be mathematically precise.

Answer: 
  **The inductive case is: P n → P (n + 1), where**
  **n is any succesive natural number.**

5. Which expression in your preceding answer
corresponds to the induction hypothesis.

Answer: 
  **(n + 1) is the inductive hypothesis. Smaller proofs**
  **build to larger proofs.**
-/




/- ****** -/
/-   #5   -/
/- ****** -/


/- #A [5 points] 

Prove the following formally. 
-/

example : ∀ (P Q : Prop), P ∧ Q → P ∨ Q :=
begin
  assume P Q,
  assume h,
  cases h,
  left,
  exact h_left,
end

/- #B [5 points] 

Prove the following formally, writing
a brief comment before each line of your
proof script describing the logical step
it implements. Then below the formal proof
give an English-language version of it.
If the second half of the proof uses the
same strategy as the first half, you can,
in English, say, "the rest of the proof
uses the same strategy," and be done.
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P :=
begin
  -- Assume the proposition P and Q
  assume P Q,
  -- Prove the proposition P ∨ Q ↔ Q ∨ P
  -- To prove a bi-implication, we need to prove
  -- both implications

  -- First, prove P ∨ Q → Q ∨ P
  split,
  -- Assume P ∨ Q 
  assume h,
  -- Under the assumption P ∨ Q, we have two cases
  cases h,
  -- Case 1: P ∨ Q is true because P is true
  right,
  exact h,
  -- Case 2: P ∨ Q is true because Q is true
  left,
  exact h,

  -- Next, prove Q ∨ P → P ∨ Q
  -- Assume Q ∨ P
  assume h,
  -- Under the assumption Q ∨ P, we have two cases
  cases h,
  -- Case 1: Q ∨ P is true because Q is true
  right,
  exact h,
  -- Case 2: Q ∨ P is true because P is true
  left,
  exact h,
  -- QED
end

/-
Proof. 

  We are to prove the proposition P ∨ Q ↔ Q ∨ P. To prove 
  a bi-implication, we need to prove the two implications
  from left to right and from right to left. 

  First, we prove P ∨ Q → Q ∨ P. To prove this implication,
  we assume the proposition P ∨ Q. Under the assumption
  we perform, we have two cases: one where P is true, and one
  where Q is true. In both cases Q ∨ P  is true because
  P is true, or Q is true.

  Then we prove Q ∨ P → P ∨ Q. This follows the same strategy as 
  above. 
  
  We have proven the bi-implication from both sides. QED. 
-/



/- ***************** -/
/-    EXTRA CREDIT   -/
/- ***************** -/

/-
We define a new polymorphic data type, 
tree. A tree is either a "twig" that 
carries a value of some type α; or a 
tree is a "root" that carries a value 
of type α and two "children,"" each 
itself such a tree. The definition is
polymorphic in the sense that values
in the tree can be of any type, α.
-/

inductive tree (α : Type)
| twig (a : α) : tree
| root (a : α ) (left right : tree) : tree

open tree

/- #A 

Define a tree, t, of natural numbers, with 0 
at the root and two sub-trees: the left is a 
twig with the value 1, and the right is a twig
with the value 2. Here's a diagram:

          0     -- root with 0 and two sub-trees
         / \
        1   2   -- twigs with 1, 2; no sub-trees
-/

def t : tree nat :=
  root 0 (twig 1) (twig 2)

/- #B

Define a function, tree_size, that takes any
tree and returns the number of values stored 
in it. For example, t stores three values (0,
1, and 2). Reminder: Put patterns in parens.
Answer by completing the partial definition 
we provide.
-/

def tree_size {α : Type} : tree α → ℕ  
| (twig v) := 1
| (root v l r) := 1 + tree_size l + tree_size r

-- test cases
example : tree_size (twig 0) = 1 := rfl
example : tree_size t = 3 := rfl


/- #C 

Here's the induction axiom for the
tree type.
-/

#check @tree.rec_on

/-
tree.rec_on :
  Π {α : Type} 
  {motive : tree α → Sort u_1} 
  (n : tree α),
    (Π (a : α), motive (twig a)) →
    (Π (a : α) 
      (left right : tree α), 
      motive left → 
      motive right → 
      motive (root a left right)) → 
    motive n

Explain in English exactly how you'd prove, by
induction, that every tree has some property P. 
Be sure to explain what specific "lemmas" have to
be proved to complete the application of the
induction axiom for tree.

Answer: 
Base case. 
  Given any motive of type tree α → Sort u_1, it 
  will suffice to show that the twig has the property P.
Inductive case. 
  Given any motive of type tree α → Sort u_1, it
  will suffice to show that the root has the property P.
QED.
-/


