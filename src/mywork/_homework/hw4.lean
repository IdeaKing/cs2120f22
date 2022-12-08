/-
CS 2120 F22 Homework #4. Due Oct 13.
-/

/- #1A [10 points]

Write a formal proposition stating that 
logical and (∧) is associative. That is, 
for arbitrary propositions, P, Q, and R,
P ∧ (Q ∧ R) is true *iff* (P ∧ Q) ∧ R is, 
too. Replace the placeholder (_) with your
answer.
-/

def and_associative : Prop := 
  ∀ (P Q R : Prop), P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R


/- #1B [10 points]

Give an English language proof. Identify
the inference rules of predicate logic
that you use in your reasoning.
-/

/-
Answer: 
It will suffice to prove the implication in each direction.
We will first consider P ∧ (Q ∧ R) → (P ∧ Q) ∧ R. We 
assume that P ∧ (Q ∧ R) is true; thus we can 
use and-elimination right to prove that "P" is true and 
that "Q ∧ R" are true. Then we can use and-elimination 
right and left to prove that Q is true and R is true. Then
we can use and-intro to prove (P ∧ Q) are true
and use and-intro again to prove (P ∧ Q) ∧ R is true. 

Next we will consider (P ∧ Q) ∧ R → P ∧ (Q ∧ R). We assume that 
(P ∧ Q) ∧ R is true; thus we can use and-elimination left to
prove that R is true. We can then use and-elimination right to 
prove that (P ∧ Q) is true. We can then use and-elimination left and 
right to prove that P is true and Q is true. Lastly we can use
and-intro to prove that (Q ∧ R) is true and that P ∧ (Q ∧ R is true).
-/

/- #1C [5 points]

Give a formal proof of the proposition.
Hint: unfold and_associative to start.
-/

theorem 
and_assoc_true: and_associative 
:=
begin
  -- each direction
  unfold and_associative,
  intros P Q R,
  apply iff.intro _ _,
  -- first direction
  assume pandqr,
  cases pandqr,
  cases pandqr_right,
  let pandq := and.intro pandqr_left pandqr_right_left,
  exact and.intro pandq pandqr_right_right,
  -- second direction
  assume pqandr,
  cases pqandr,
  cases pqandr_left,
  let qandr := and.intro pqandr_left_right pqandr_right,
  exact and.intro pqandr_left_left qandr,
end



/- #2A [10 points]

Write the proposition that ∨ is associative.,
analogous to the proposition about ∧ in #1.
-/

def or_associative : Prop := 
  ∀ (P Q R : Prop), P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R


/- #2B [10 points]

Write an English language proof of it, citing
the specific inference rules you use in your
reasoning.

Answer: 

It will suffice to prove the biimplication in each direction.
Firstly, we will prove from the right, we can use or elim left
to prove P is true, and use or elim left and right to prove Q R,
Then we can use or intros to prove p or q and (p or q) or r.

Secondly we will prove from the left, we can use or elim right to prove R,
and we can use or elim left and right to prove P or Q. Then we can use 
or_intros to prove P or Q and (p or q) or r.

Then we have proven the biimplication.
-/


/- #2C [5 points]

Complete the following formal proof.
-/

theorem or_associative_true : or_associative :=
begin
  unfold or_associative,
  intros P Q R,
  apply iff.intro _ _,

  assume direction1,
  cases direction1 with p QorR,
  let left := or.intro_left Q p,
  exact or.intro_left R left,

  cases QorR with q r,
  let PorQ := or.intro_right P q,
  exact or.intro_left R PorQ,
  exact or.intro_right (P ∨ Q) r,

  assume direction2,
  cases direction2 with PorQ r,
  cases PorQ with p q,
  exact or.intro_left (Q ∨ R) p,

  let QorR := or.intro_left R q,
  exact or.intro_right P QorR,
  let QorR := or.intro_right Q r,
  exact or.intro_right P QorR,
end


/- #3A [10 points]
Write a formal statement of the proposition.
-/

def arrow_transitive : Prop :=
  ∀ (X Y Z: Prop), (X → Y) → (Y → Z) → (X → Z)


/- #3B [10 points]

Write an English language proof of the proposition
that for any propositions, X, Y, and X, it's the
case that (X → Y) → (Y → Z) → (X → Z). In other
words, implication is "transitive." Hint: Recall
that if you have a proof of, say, X → Y, and you 
have a proof of X, you can derive a proof of Y by
arrow elimination. Think of it as applying a proof
of an implication to a proof of its premise to get
yourself a proof of its conclusion.

Answer:

It suffices to show that whenever the context is true,
the conclusion is true too. We should start by assuming 
that X implies Y, and that Y implies Z. Then we can prove
that X is true. We can then use arrow elimination to conclude
that Y is true, because it follows from X implies Y. Lastly
we can conclude that Y is true because Y implies Z from 
arrow elimination to prove that Z is true.
-/


/- #3C [5 points]. 
Write a formal proof of it.
-/

theorem arrow_transitive_true : arrow_transitive :=
begin
  unfold arrow_transitive,
  assume X Y Z,
  assume XtoY YtoZ,
  assume x,

  exact YtoZ (XtoY x)
  -- ???
end

/- #4
Suppose that if it's raining then the streets
are wet. This problem requires you to prove that
if the streets are not wet then it's not raining.
-/

/- #4A [10 points]

Start by writing the proposition in predicate
logic by completing the following answer.
-/

def contrapositive : Prop :=
  ∀ (Raining Wet : Prop), (Raining → Wet) → (¬Raining → ¬Wet)


/- #4B [10 points]. 
-/

theorem contrapositive_valid : contrapositive :=
begin
  unfold contrapositive,
  assume r w,
  assume r_then_w,
  assume not_r,
  assume not_w,
  exact not_r (r_then_w r),

  -- ?
end

/- #4C [5 points]. 

Give an English language proof of it.

If raining implies wet then not raining implies not wet. 
If we can prove that the streets are not wet then
its not raining. If we assume that the street is dru
then we can show that it would not be possible to rain. 
We can prove that if the rain leads to having a wet street
and the street is not wet, then it is not raining.
-/
