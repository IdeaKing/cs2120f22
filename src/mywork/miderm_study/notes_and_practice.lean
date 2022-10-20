/-
***Lean***
  Sections:
    Preventing repeating:
      Create a section and declare all variable names.
      Lean will implicitly add ∀ (variable : Prop).
    Syntax:
      section section_name
      variables var1 var2 ... : Prop

  Implicit type judgements:
    Lean can determine the type by the types of the 
    variables that follow.

  Applying functions:
    Syntax:
      P s
      "s" is applied to proof "P"
  
  #check  
    Checks for syntax errors. 
    If it's syntactically correct, it tells you its type. 
  
  def
    Establishes a new definition
      A binding of a variable to a value of a specified type
    
    Example:
      def proof_of_true : true := true.intro
  
  let 
    Supports bindings of values to local variables, followed by
    evaluation of an expression that uses that local variable.  
  
  variable
    Declares a new variable an it's type without binding a value 
    to it. 

    Example:
      variable Person : Type    -- Person is some data type
      variable Likes : Person → Person → Prop -- Likes is a 2 argument predicate
      variables (Mary Margo : Person)  -- p and q are variables of type Person
      variable likes_mary_margo : Likes Mary Margo -- likes_mary_margo is a proof of 

  eval/#reduce
    Asks Lean to actually evaluate expressions and report that reduce. 
    eval is more efficient than #reduce
-/

/-
***Proof Tactics***
  cases
    Applies elimination rules to a term appropriate to its
    type. 
  
    Example:
      def cases1 : Prop := 
        ∀ (P Q : Prop), P ∧ Q → P 
      
      example : cases1  :=
      begin
        unfold cases1,
        assume P Q,
        assume h,
        let p : P := and.elim_left h,
        exact p,
      end

      example : cases1 :=
      begin
        unfold cases1,
        assume P Q,
        assume h,
        cases h with p q,
        exact p,
      end

    Using Cases with Classical Logic:
      cases (classical.em P) with p np

  assume and intro(s)
    Apply ∀ and → introduction rules
  
  exact
    Meant to be given a complete proof term
    with no remaining holes. 
  
  apply
    will accept a complete proof term but 
    can be used with proof terms with holes.
-/

/-
***Inference rules in Lean***

  -- AND
  #check @and.intro       -- ∀ {a b : Prop}, a → b → a ∧ b
  #check @and.elim_left   -- ∀ {a b : Prop}, a ∧ b → a
  #check @and.elim_right  -- ∀ {a b : Prop}, a ∧ b → b

  -- OR
  #check @or.inl          -- ∀ {a b : Prop}, a → a ∨ b
  #check @or.inr          -- ∀ {a b : Prop}, b → a ∨ b
  #check @or.intro_left   -- ∀ {a : Prop} (b : Prop), a → a ∨ b
  #check @or.intro_right  -- ∀ (a : Prop) {b : Prop}, b → a ∨ b
  #check @or.elim         -- ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c

    Use inl or inr when Lean can infer the other disjunct,
    otherwise use intro_left or intro_right, where you have
    to give the other disjunct (a proposition, not a proof)
    as an explicit argument.
  
  -- NOT
    #check @classical.by_contradiction  -- ∀ {p : Prop}, (¬p → false) → p

  -- IFF
    #check @iff.intro     -- ∀ {a b : Prop}, (a → b) → (b → a) → (a ↔ b)
    #check @iff.mp        -- ∀ {a b : Prop}, (a ↔ b) → a → b
    #check @iff.mpr       -- ∀ {a b : Prop}, (a ↔ b) → b → a

   FORALL ARROW
    Rather, you prove a forall or arrow proposition by 
    *defining a function* that takes a value/proof of the 
    premise/argument and that returns a value/proof of the 
    conclusion. On the other hand, forall/arrow elimination 
    is by *applying such a "function/proof" to an argument 
    of the right kind to obtain a result of the right kind.
-/

/-
***Constructive logic V First order logic***
  Constructive logic:
    0. We can construct rules of logic naturally.
    1. Can quantify over types, predicates, and functions
    2. We can treat proofs as functions
      A proof can be taken as a function with *n* amount of input 
      propositions.
      Proofs are computational.
  First order logic:
    1. Can not quantify over types, predicates, and functions
    2. 
-/

/- 
***Inference Rules:***

**And:**
  And Introduction:
    def and_introduction := X → Y → (X ∧ Y)

  And Elim Left:
    def and_elim_left  := X ∧ Y → X  

  And Elim Right:
    def and_elim_right := X ∧ Y → Y 

**Or**
  Or Intro Left:
    def or_intro_left := X → X ∨ Y

  Or Intro Right
    def or_intro_right := Y → X ∨ Y

  Or Elim
    def or_elim := (X ∨ Y) → (X → Z) → (Y → Z) → Z

**Iff**
  Iff intro:
    def iff_intro := (X → Y) → (Y → X) → X ↔ Y

    Description:
      If you have a proof of X → Y, and you have a proof of
      Y → X, you can derive a proof of X ↔ Y.

      **Proving Equivalence**
        It will suffice to prove the implication in each
        direction. We first consider X → Y, provide a proof.
        Next we will consider Y → X, provide a proof. Having 
        proven the implication in each direction we've 
        completed our proof.

  If Elim Left:
    def iff_elim_left := X ↔ Y → (X → Y)

  If Elim Right:
    def iff_elim_right := X ↔ Y → (Y → X)

**For all and arrow**
  For all and arrow equivalence (Intro):
    def arrow_all_equiv := (∀ (x : X), Y) ↔ (X → Y)

    Description:
      We have an arbitrary but specific proof of X, and
      in that context we can derive a proof of Y.

    In Lean:
      ∀ (x : X), Y && X → Y is the same
      From any proof of X, we can derive a proof of Y.

  Arrow Elimination:
    def arrow_elim := (X → Y) → X → Y
    def all_elim   := ∀ (x : X), Y) → X → Y

    Description:
      If from a proof of X you can derive a proof of Y, 
      and if you have a proof of X you can derive a 
      proof of y.

      Example:
        If every ball is blue, 
        and b is some arbitrary but specific ball,
        b is blue.

        **Universal Generalization**
          Showing that something is true of every 
          object of a particular kind. 

          (∀ (b : B), isBlue)
            For any Ball b, b is blue. 
            B is "Ball"
            b is an arbitrary but specific ball
            isBlue "b is Blue"
          
          Higher order predicate logic:
            Applying a proof of an universal generalization
            to a specific object yields a proof of the 
            generalization *specialized* to that particular
            object. 

    Lean as a coding language:
      Type - is a set of possible values and a set of allowed operations on it.
        func f(s) -> nat
          formally:
            (f : string -> nat)

        Applying functions in Lean:
          f(s) → f s

      Arrow Elimination:
        P and Q are arbitrary propositions. 
        
        Example: P → Q
          pq is the proof of P → Q
          pq's type: (pq : P → Q)

        The proof "pq" can be considered a function.
          It takes proposition P and returns proposition Q.

        We have proof pq: (pq : P → Q) and (p : P), because we have a 
        proof of P, then (pq p) is a proof of Q.
          If P → Q is true, and P is true, then Q must be true.

**True and False**
  True Intro:
    Propositional: Always evaluates to boolean True
    Predicate: A proposition that is invariably judged to be true

    Example:
      1. (X ∧ true) → True

    Proving True:
      theorem true_is_true : true := true.intro
      -- there is always a proof of true
      -- the proposition is true
      -- the proof is true.intro

  Definition of False:
    Propositional: Always evaluates to boolean False
    Predicate: A proposition that is invariably judged to be false
      *A proposition that has no proofs*
        Because there are no proofs, there is no introduction rule

    Example:
      1. (X ∨ False) → True 

  False Elimination (Proof by Negation):
    false.elim

    In Propositional Logic:
      false → X ⊢ True
        Anything from false follows. 

        If we can prove false, then you can 
        deduce anything at all is true. 
          If false is true, then even if a proposition
          P is false, false is true, so P is true too.
            -- Application of universal specialization?

**Not**
  Definition of Not:
    When is ¬P → True?
      When P → False
      *When there are no proofs of P*
    
    Thus:
      ¬P ↔ (P → false)

      If there is a proof of P, then from it we can
      derive an impossibility, so there must be no 
      proof of P. 
  
  **Proof by Negation**
    Assume P is true, and show that from this assumption 
    you can derive a contradiction and we contain a proof
    of false. 

    Negation Elimination:
      def negation_elim := ¬¬X → X
      In Lean: classical.by_contradiction
        ∀ (P : Prop), ¬(¬P) → P

      We use negation elimination to prove that when
      ¬P is false, ¬¬P is P. 

      *Negation Elimination can only be proven if we assume*
      *the Law of the Excluded Middle.*

      **The Law of the Excluded Middle**
        It is an universal generalization, so it can be
        applied to any proposition. 

        Once applied em, we can perform case analysis of 
        each outcome to prove the goals. 

    Using Negation Elimination:
      If we want to prove P:
        It will suffice to prove ¬¬P, for if you do that,
        you just apply negation elimination to prove P. 
      
      If you apply negation elimination, the new goal is
      to prove ¬¬P which means that ¬P → false. 

    False Elimination: You can ignore the consequences of 
    situations that can never even happen in the first place.
-/

-- Practice 1: Arrow Elim.
def arrow_trans : Prop := 
  ∀ (X Y Z : Prop), (X → Y) → (Y → Z) → (X → Z)

example : arrow_trans :=
begin
  unfold arrow_trans,
  assume X Y Z,
  assume x_imp_y y_imp_z x,

  let y := x_imp_y x,
  let z := y_imp_z y,
  exact z,
end

-- Practice 2: False Elim.
def no_contradiction : Prop :=
  ∀ (X : Prop), ¬(X ∧ ¬X)

example : no_contradiction :=
begin
  unfold no_contradiction,
  assume X,
  assume h,
  
  let not_x := and.elim_right h,
  let x := and.elim_left h,

  contradiction,
end

-- Practice 3: False Elim. 
def contrapostitive : Prop :=
  ∀ (X Y : Prop), (X → Y) → (¬Y → ¬X)

example : contrapostitive :=
begin 
  unfold contrapostitive,
  assume X Y,
  assume x_imp_y,
  assume not_y,
  assume x,

  let y := x_imp_y x,
  apply false.elim (not_y y),
  -- orrrr
  -- contradiction,
end

-- Practice 4: False Elim
def demorgan1 : Prop := 
  ∀ (X Y : Prop), ¬(X ∨ Y) ↔ ¬X ∧ ¬Y

example : demorgan1 :=
begin
  unfold demorgan1,
  assume X Y,
  apply iff.intro,

  -- Provide a proof in the first direction
  -- Assume the precendent and then prove the 
  -- antecedent in that context.
  assume not_xory,
  apply or.elim (classical.em X),
  assume x,
  let x_or_y : X ∨ Y := or.inl x,
  contradiction,

  assume not_x,
  apply or.elim (classical.em Y),
  assume y,
  let not_x_or_y : X ∨ Y := or.inr y,
  contradiction,

  assume not_y,
  apply and.intro,
  assume x,
  contradiction,
  assume y,
  contradiction,

  -- Provide the proof in the other direction. 
  -- Since it is an implication, we will assume 
  -- ¬X ∧ ¬ Y and prove ¬(X ∨ Y) under this 
  -- context. 
  assume not_x_and_not_y,
  -- ¬(X ∨ Y) ↔ X ∨ Y → false
  -- So we assume X ∨ Y
  assume x_or_y,
  cases x_or_y,

  -- We can derive ¬X using and elimination
  let not_x := and.elim_left not_x_and_not_y,
  -- ¬X and X are in the same context ∴ contradiction
  contradiction,

  -- We can obtain ¬Y using and elimination
  let not_y := and.elim_right not_x_and_not_y,
  -- ¬Y and Y are in the same context ∴ contradiction
  contradiction,
end

-- Practice 5: False Elim
def demorgan2 : Prop := 
  ∀ ( X Y : Prop), ¬(X ∧ Y) ↔ ¬X ∨ ¬Y

example : demorgan2 :=
begin
  unfold demorgan2,
  assume X Y,
  apply iff.intro,

  -- Direction 1
  assume not_x_and_y,
  cases (classical.em X) with x not_x,
  cases (classical.em Y) with y not_y,

  let x_and_y := and.intro x y,
  contradiction,

  apply or.inr,
  assume y,
  contradiction,

  apply or.inl,
  assume x,
  contradiction,

  -- Direction 2
  assume not_x_or_not_y,
  assume x_and_y,

  let x := and.elim_left x_and_y,
  let y := and.elim_right x_and_y,

  cases not_x_or_not_y,
  contradiction,
  contradiction,
end

-- Practice 6: Challenge?
def em_equiv_pbc : Prop :=
  ∀ (P : Prop), (P ∨ ¬P) ↔ (¬¬P → P) 

example : em_equiv_pbc :=
begin
  unfold em_equiv_pbc,
  assume P,
  apply iff.intro,

  -- Direction 1
  assume p_or_not_p,
  assume not_not_p,
  cases p_or_not_p with p not_p,
  exact p,
  contradiction,

  -- Direction 2
  assume not_not_p_imp_p,
  cases (classical.em P),
  apply or.inl,
  exact h,

  apply or.inr,
  assume p,
  contradiction,
end

-- Review 1
def and_associative : Prop := 
  ∀ (P Q R : Prop), P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R

example : and_associative :=
begin
  unfold and_associative,
  assume P Q R,
  apply iff.intro,

  assume pqr,
  let p := and.elim_left pqr,
  let q_and_r := and.elim_right pqr,
  let q := and.elim_left q_and_r,
  let r := and.elim_right q_and_r,
  let p_and_q := and.intro p q,
  let p_and_q_and_r := and.intro p_and_q r,
  exact p_and_q_and_r,

  assume pqr,
  let r := and.elim_right pqr,
  let p_and_q := and.elim_left pqr,
  let p := and.elim_left p_and_q,
  let q := and.elim_right p_and_q,
  let q_and_r := and.intro q r,
  let p_and_q_and_r := and.intro p q_and_r,
  exact p_and_q_and_r,
end

-- Review 2
def or_associative : Prop := 
  ∀ (P Q R : Prop), P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R

example : or_associative :=
begin
  unfold or_associative,
  assume P Q R,
  apply iff.intro,

  assume pqr,
  cases pqr with p qr,
  apply or.inl,
  apply or.inl,
  exact p,

  cases qr with q r,
  apply or.inl,
  apply or.inr,
  exact q,

  apply or.inr,
  exact r,

  assume pqr,
  cases pqr with pq r,
  cases pq with p q,
  apply or.inl,
  exact p,

  apply or.inr,
  apply or.inl,
  exact q,

  apply or.inr,
  apply or.inr,
  exact r,
end