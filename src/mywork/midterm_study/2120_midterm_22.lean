-- Thomas Chia, UJS4RC
/-
This is the CS2120 (Sullivan) midterm exam. 

The exam has 100 points total distributed over four
multi-part questions. There's an extra credit question
at the end. Points for each part are indicated.
-/

-- ****************** #1 [30 points] *******************

/- A. [5 points] 

Is it true in predicate logic that  
(false → true) ∧ (false → false)?
Answer: 
    It is True.

-/

/- B. [10 points] 

Give a formal proof by completing the 
following "example" in Lean, or state 
in English that there is no such proof.

-/

example : (false → true) ∧ (true → true) :=
begin
    split,
    {
        assume f,
        exact true.intro,
    },
    {
        assume t,
        exact true.intro,
    }
end


/- C [15 points]. 

Give an English language proof of the proposition. 
Identify each inference  rule you use at each point
in your argument. For example, at a certain point 
you might say something like this: By the ____ rule, 
it will suffice to show ____. Then you would go on
to show that what remains to be proved is valid. 


Answer: 
    We can use and elimination left to obtain (false → true),
    and we can use and elimination right to obtain (true → true).

    False implies true is true by implication introduction.
    True implies true is true by implication introduction.

    True and true is true by and introduction. Therefore,
    the proposition is true.


-/


-- ****************** #2 [30 points] *******************


/- 
"Resolution" is an inference rule that we 
haven't talked about before. It's valid in
propositional, classical, and constructive
predicate logic. We will present the rule,
in both propositional and predicate logic,
and will ask you to prove that is's valid
in each case.


In propositional logic, the resolution rule 
is ¬P ∨ Q, P ⊢ Q. To check its validity, we 
can write it as  (¬P ∨ Q) ∧ P → Q. Note: ∧ 
has higher precedence than →, so there are 
implicit parentheses around (¬P ∨ Q) ∧ P, 
making the overall proposition an implication.
-/


/- A. [5 points].

Give a brief English language explanation why this
inference rules makes sense: not a rigorous proof,
just an explanation of why Q has to be true under
the conditions give by the assumptions/premises.

Answer: 
    The resolution rule makes sense because if P is true, 
    or false Q is true. Furthermore, if Q is true or false,
    Q is still true, so it is a valid rule. 

    Furthermore, if we take the negation of inference
    rule, it is unsatisfiable, thus making every 
    interpretation of the inference rule true, and 
    therefore valid.

-/



/- B. [5 points]

Prove that this inference rule is valid in
propositional logic by giving a truth table for it. 
We'll give you a start. Fill in the rows then state
how you know from the truth table that the overall
proposition is valid.

P   Q   (¬P ∨ Q)    (¬P ∨ Q) ∧ P    ((¬P ∨ Q) ∧ P) → Q
------------------------------------------------------
f   f   t           f               t
t   f   f           f               t
f   t   t           t               t
t   t   t           t               t

Statement: 
    The proposition is valid because all interpretations of 
    p and q result in the proposition being true.

-/  


/- C. [10 points] 

Give a formal proof that the inference rule is 
valid in our constructive predicate logic. Fill
in a proof script here to construct your proof.
Hint: remember that the cases tactic applied to
a proof of a conjunction applied and.elim both
left and right, and when applied to a proof of 
a disjunction gives you two cases to consider,
where you need to show that the remining goal
is true in either case. 
-/

example : ∀ (P Q : Prop), (¬P ∨ Q) ∧ P → Q :=
begin
    assume P Q,
    assume not_p_or_q_and_p,

    cases not_p_or_q_and_p with not_p_or_q p,
    cases not_p_or_q with not_p q,

    contradiction,
    exact q,
end


/-
D. [10 points] Give an informal (English) proof 
that the inference rule is valid in predicate logic. 
Name each inference rule you use in your reasoning.

Answer:
    We have a proof of P and a proof of Q. 

    We have an implication so we must assume that (¬P ∨ Q) ∧ P is true, 
    and from there derive a proof of Q. 

    We apply and elimination right to (¬P ∨ Q) ∧ P to get a proof of P 
    and a proof of (¬P ∨ Q).

    We apply or elimination to (¬P ∨ Q) and we prove that Q is true through 
    contradiction using case analysis.

-/


-- ****************** #3 [20 points] *******************


/- 
A. [10 points]. Write formally (in constructive logic) 
the proposition that, for any propositions P and Q, if 
P is equivalent to Q (iff), then if P is true, then Q
is true.  Hint: put parentheses around your ↔ expression. 
-/

-- Don't try to write a proof here; just the proposition
def if_p_iff_q_then_if_also_p_then_q : Prop :=
    ∀ (P Q : Prop), (P ↔ Q) → (P → Q)


/-
B. [10 points] Give *either* a precise, complete English
language proof that this proposition is valid, naming 
each inference you you use in your reasoning, *or* give 
a formal proof of it using Lean. You do not have to give
both. 
-/

example : if_p_iff_q_then_if_also_p_then_q :=
begin
    unfold if_p_iff_q_then_if_also_p_then_q,
    assume P Q,
    assume p_iff_q,
    assume p,

    -- cases p_iff_q with p_implies_q q_implies_p,
    -- let q := p_implies_q p,

    have q := iff.mp p_iff_q p,
    exact q,
end




-- ****************** #4 [20 points] *******************

/- #



A. [10 points] Suppose P is any proposition. In plain
English give a step by step explanation of how you would 
go about proving ¬P using proof *by negation*. 

Answer:
    We asuume that P is true and from this assumption
    we can derive a contradiction, which is a proof of false. 
    Since there can be no proof of false, ¬P is therefore true.

-/


/- B. [10 points] 

In plain English explain each step in a proof of P
*by contradiction*. Identify where a proof by negation 
(¬ introduction) occurs in the proof by contradiction. 
Explain what classical rule of inference you need to 
use to finish off such a proof. 

Answer: 
    To prove P → true, we would assume that ¬P → true. 

    To do so, we assume that not P is true, and from this 
    assumption we derive a contradiction. Thus proving 
    that ¬P is false - which is another way of saying 
    ¬¬P. 

    We then use negation elimination to prove that ¬¬P → P. 
    Thus, P is true.

-/



/- Extra Credit [10 points for all three answers correct]

Suppose that "if it's sunny, it's hot, and also that if 
it's not sunny, it's hot. 

(s → h) ∧ (¬s → h) 
t → t ∧ f → t
A. Is it hot in classical logic? 

Answer: 
    Yes, it is hot in classical logic.


B. Is it hot "constructively?" Briefly explain your answer. 

Answer: 
    It is hot constructively because we can prove that
    it is hot by assuming that it is sunny, and then
    proving that it is hot.


C. Give a formal proof of your answer to the classical question. 
Use S and H as names to stand for the propositions, "it's sunny" 
and "it's hot," where S stands for "it's sunny" and H stands for
"it's hot."
-/

-- it's hot
example : ∀ (S H : Prop), (S → H) → (¬S → H) → H :=
begin
    assume S H,
    assume sh nots_h,

    cases classical.em S with s not_s,
    cases classical.em H with h not_h,

    exact h,

    let hot := sh s,
    contradiction,

    let hot := nots_h not_s,
    exact hot,
end

