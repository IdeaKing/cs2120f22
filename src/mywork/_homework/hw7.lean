import data.set

/- #1

Formally prove that if there's an object, a, of some 
type, α, having some property (satisfying a predicate), 
P, then not every object of type α fails to have property, 
P. Add a brief comment before each line of your proof 
script to provide what amounts to the outline of a good
English language proof.
-/

example (α : Type) (P : α → Prop) :
  (∃ a, P a) → (¬(∀ x, ¬ P x)) 
  :=
begin
  -- assume there exists an object, a, of type α that has property P
  assume h,
  -- assume that every object of type α fails to have property P
  -- (this is the negation of the hypothesis)
  cases h with a ha,
  -- assume that every object of type α fails to have property P
  assume h,
  -- show that the object, a, of type α that has property P fails to have property P
  have hna : ¬ P a := h a,
  -- contradition
  contradiction
end


/- Extra credit. 

The converse of this proposition is clasically true. If
not every object lacks propery, P, then there must be some
object that has it. If you try to prove the converse in
our constructive logic, what happens? Show you work, and
then briefly but clearly explain exactly what goes wrong.
-/



/- #2

Consider the following binary relation, r, with domain
and co-domain both being ℕ. For each following question,
answer yes/no then briefly justify your answer.

( domain = ℕ, r = {(0,0),(1,1),(2,2)}, co-domain=ℕ )

A. Is this relation reflexive? Yes because all elements are linked to themselves
B. Is this relation symmetric? Yes because every relation has an inverse
C. Is this relation transitive? Yes becayse every relation is linked to itself
D. Is this relation an equivalence relation? Yes because a b and c are true
-/



/- #3

A binary relation, r, is said to be *anti-symetric* 
if, for all values in its domain, a and b, if r a b 
and if r b a then a = b. Give an example of a familiar
arithmetic relation that's anti-symmetric, and briefly
explain why it's so.

  Subtraction. Because if a - b = 0 then b - a = 0 so a = b.
-/


/- #4
A binary relation, r, is said to be *asymmetric* if
whenever, for any a and b, if r a b then ¬ r b a. Be
careful to note that asymmetry and antisymmetry are
different properties.  Answer each of the following 
sub-questions. We give you a formal definition of anti
-/

def is_asymmetric 
  {α : Type} 
  (r : α → α → Prop) : Prop 
  := ∀ (a b : α), r a b → ¬ r b a 

/- A.

Name a familar arithmetic relation that's asymmetric
and briefly explain why you think it's asymmetric.

Answer here:
  Greater than. Because if a > b then b < a is false.
-/

/- C: 

An object cannot be related to itself in an asymmetric
relation. First, complete the following informal proof
of this statement.

Proof: Assume α, r, and a are as given (and in particular
assume that r is asymmetric). Now assume r a a. <finish
the proof>.

Answer here (rest of proof): 
  This is a contradiction because r a a implies ¬ r a a which is false.
-/

/- D.

Now prove a closely related proposition formally. 
Add a comment to each line of your formal proof 
so as to construct a good skeleton for a fluent 
English language proof.
-/

example
  (α : Type) 
  (r : α → α → Prop)
  (h : is_asymmetric r) :
¬ ∃ (a : α), r a a :=
begin
-- proof by negation
  assume h,
  cases h with a ha,
  have hna : ¬ r a a := h a a ha,
  contradiction,
end


/- #5
Prove that equality on an inhabited (non-empty) type 
is not assymetric. In the following formalization we
assume there is a value (a : α), which establishes 
that α is inhabited.
-/

example (α : Type) (a : α): ¬ is_asymmetric (@eq α) :=
begin
  assume h,
  have hna : ¬ a = a := h a a rfl,
  contradiction,
end

/- Extra credit: What exactly goes wrong in a formal 
proof if you drop the "inhibitedness" condition? Give
as much of a formal proof as you can then explain why
it can't be completed (if it can't!).
-/



/- #6
Two natural numbers, p and q, are said to be 
"equivalent mod m" if p % m = q % m, which makes
"equivalence mod m" a binary relation on natural
numbers. Here's a formal definition of this binary
relation on the natural numbers (given an m).
-/

def equiv_mod_m (m : ℕ) : ℕ → ℕ → Prop := 
  λ p q : ℕ, p % m = q % m

/-
Prove using Lean's definition of "equivalence" that 
equiv_mod_m is an equivalence relation for any natural
number, m. Here you'll also use Lean's definitions of
reflexive, symmetric, and transitive. They are as we
have covered in class. 
-/

example : ∀ m : ℕ, equivalence (equiv_mod_m m) :=
begin
  assume m,

  split,

  unfold reflexive,
  assume x,
  unfold equiv_mod_m,

  split,

  unfold symmetric,
  unfold equiv_mod_m,
  assume x y,

  assume h,
  exact eq.symm h,

  unfold transitive,
  unfold equiv_mod_m,

  assume x y z,
  assume h1 h2,

  apply eq.trans h1 h2,
end



/- #7
Consider the relation, tin_rel, that associates people 
with U.S. taxpayer id numbers, which we'll represent as 
natural numbers here. 

Assume this relation is single-valued. Which of the 
following properties does this relation have? Give
a very brief justification of each answer. Assume
the domain is all living persons, and the co-domain
is all natural numbers.

-- it's a function: yes
-- it's total: yes
-- it's injective (where "): yes
-- it's surjective (where the co-domain is all ℕ): no
-- it's strictly partial: no
-- it's bijective: no
-/



/- #8
Suppose r is the empty relation on the natural 
numbers. Which of the following properties does
it have? Explain each answer enough to show you
know why your answer is correct.

-- reflexive: no because there are no natural numbers linked to themselves
-- symmetric: yes because there this is not true r a b iff r b a
-- transitive: yes because this is there isnt a case where this follows: r a b and r b c imples r a c
-/



/- #9
Here's a formal definition of this empty relation.
That there are no constructors given here means there 
are no proofs, which is to say that no pair can be 
proved to be in this relation, so it must be empty.
-/

inductive empty_rel : ℕ → ℕ → Prop

/-
Formally state and prove you answer for each of the
three properties. That is, for each property assert
either that empty_rel does have it or does not have it, 
then prove your assertion. Include English-language 
comments on each line to give the essential elements 
of a good English language proof.
-/


example : ¬reflexive empty_rel :=
begin
unfold reflexive,
-- Proof by negation
assume h,
-- We choose a number 0 to prove that there is no proof
-- of empty_rel 0 0
let x := h 0,
-- We have a proof of empty_rel 0 0, which is a contradiction
cases x,
end

example : symmetric empty_rel :=
begin
unfold symmetric,
-- We make an assumption that empty_rel is symmetric
assume a b h,
-- We have a proof of empty_rel a b, which is a contradiction
cases h,
end

example : transitive empty_rel :=
begin
-- We make an assumption that empty_rel is transitive
assume a b c h k,
-- We have a proof of empty_rel a b, which is a contradiction
cases h,
end

/- #10
A relation, r, is said to have the property of being 
a *partial order* if it's reflexive, anti-symmetric,
and transitive. Give a brief English language proof 
that the subset relation on the subsets of any set, 
S (of objects of some type), is a partial order. 

Pf:  
Suppose S is a set, with a ⊆ S and b ⊆ S subsets. Then

1. Transitive: If a ⊆ S and b ⊆ S and c ⊆ S then a ⊆ b and b ⊆ c implies a ⊆ c.
2. REflexive: If a ⊆ S then a ⊆ a.
3. Anti-symmetric: If a ⊆ S and b ⊆ S then a ⊆ b and b ⊆ a implies a = b.

QED.
-/



/- #11 
Finally we return again to DeMorgan's laws, but
now for sets. You'll recall that these "laws" as we
have seent them so far tell us how to distribute ¬  
over ∨ and over ∧. You will also recall that set
intersection (∩) is defined by the conjunction (∧) 
of the membership predicates, set union (∪) by the
disjunction (∨), and set complement (Sᶜ for a set,
S), by negation (¬). It makes sense to hypothesize 
that we can recast DeMorgan's laws in terms of the
distribution of complement over set union and set
intersection. Indeed we can. Your job is to state
and prove (formally) the first DeMorgan laws for 
sets, which states that the complement of a union
of any two sets equals the intersection of their 
complements.

Hint: To prove that two sets are equal, S = T, use
the ext tactic. It applies a bew axiom (called set 
extensionality) that states that to prove S = T it 
suffices to prove S ↔ T, viewing the sets as being
defined by their logical membership predicates. You
know how to handle bi-implications. The rest you 
can do by seeing "not," "and," and "or" in place 
of complement, conjunction, and disjuction, resp.  
-/

example 
  (α : Type) 
  (a b: set α) :
  (a ∪ b)ᶜ = aᶜ ∩ bᶜ := 
begin
  ext,
  split,
  assume h,
  split,
  assume h1,
  have h2 := or.inl h1,
  have h3 := h h2,
  exact h3,
  assume h1,
  have h2 := or.inr h1,
  have h3 := h h2,
  exact h3,
  assume h,
  assume h1,
  cases h1,
  have h2 := h.1 h1,
  exact h2,
  have h2 := h.2 h1,
  exact h2,
end


