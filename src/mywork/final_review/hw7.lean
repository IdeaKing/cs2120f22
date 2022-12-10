import data.set

/- #1

Formally prove that if there's an object, a, of some 
type, α, having some property (satisfying a predicate), 
P, then not every object of type α fails to have property, 
P. Add a brief comment before each line of your proof 
script to provide what amounts to the outline of a good
English language proof.
-/

example (α : Type) (P : α → Prop) : (∃ a, P a) → (¬(∀ x, ¬ P x)) :=
begin
  -- assuming the implication
  assume h,
  -- extract a witness, a, from h
  cases h with a ha,
  -- assume the negation of the implication
  assume h,
  -- show that the negation is false
  have hna : ¬ P a := h a,
  -- contradiction
  contradiction,
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

A. Is this relation reflexive? 

  **No, not every element is related to itself, only some elements are.**

B. Is this relation symmetric? 

  **Yes, if a is related to b, then b is related to a.**

C. Is this relation transitive? 

  **Yes, under all cases where a is related to b and b is related to c,**
  **a is related to c.**

D. Is this relation an equivalence relation? 

  **No, it is not all reflexive, symmetric, or transitive.**
-/



/- #3

A binary relation, r, is said to be *anti-symetric* 
if, for all values in its domain, a and b, if r a b 
and if r b a then a = b. Give an example of a familiar
arithmetic relation that's anti-symmetric, and briefly
explain why it's so.
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

  **< because, if a is related to b, then not b is not related to a.**

-/

/- C: 

An object cannot be related to itself in an asymmetric
relation. First, complete the following informal proof
of this statement.

Proof: Assume α, r, and a are as given (and in particular
assume that r is asymmetric). Now assume r a a. <finish
the proof>.

Answer here (rest of proof): 

  **If r a a were to be asymmetric, then ¬r a a would be**
  **true, however, it is false by contradiction**
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
  -- extract a witness, a, from h
  cases h with a ha,
  -- show that the negation is false
  have hna : ¬ r a a := h a a ha,
  -- contradiction
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
  -- proof by negation
  assume h,
  unfold is_asymmetric at h,
  -- apply h to a and a
  have hna := h a a,
  have haa := hna (eq.refl a),
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
  unfold equivalence,
  split,

  unfold reflexive,
  unfold equiv_mod_m,
  assume x,
  have h : x % m = x % m,
  refl,
  exact h,

  split,
  unfold symmetric,
  unfold equiv_mod_m,
  assume x y hxy,
  have h : y % m = x % m,
  rw hxy,
  exact h,

  unfold transitive,
  unfold equiv_mod_m,
  assume x y z hxy hyz,
  have h : z % m = y % m,
  rw hyz,
  rw hxy,
  exact hyz,
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

-- it's a function: 

  **Yes, because it is single-valued.**

-- it's total: 

  **No, because not everyone has a tin_rel**

-- it's injective (where "): 

  **Yes, because no-one can have the same ssn or tn**

-- it's surjective (where the co-domain is all ℕ):

  **NO, not all ℕs are ssn's**

-- it's strictly partial:  

  **Yes because not everyone has a tin_rel**

-- it's bijective: 
-/



/- #8
Suppose r is the empty relation on the natural 
numbers. Which of the following properties does
it have? Explain each answer enough to show you
know why your answer is correct.

-- reflexive:
-- symmetric: 
-- transitive:
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
assume h,
let x := h 0,
cases x,
end

example : symmetric empty_rel :=
begin
unfold symmetric,
assume a b h,
cases h,
end

example : transitive empty_rel :=
begin
assume a b c h k,
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

1. 
2. 
3. 

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
  apply and.intro,
  assume x_in_a,

  let x_in_a_or_b : (x ∈ a ∪ b) := 
    begin
      left,
      exact x_in_a,
    end,
  contradiction,
  
  assume x_in_b,
  let x_not_in_a_or_b : (x ∈ a ∪ b) := 
    begin
      right,
      exact x_in_b,
    end,  
  contradiction,

  assume h,
  cases h with h1 h2,
  assume x_in_a_or_b,
  cases x_in_a_or_b with x_in_a x_in_b,
  contradiction,
  contradiction,
  
end


