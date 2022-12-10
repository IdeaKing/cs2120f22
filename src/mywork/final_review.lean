import data.set

/-
- existence propositions and proofs
  -- introduction rule
    -- exists.intro
    -- All you need is a proof of the proposition
  -- elimination rule
  -- proofs involving existence
  -- mixed quantififier propositions
-/

/-
- set theory
  -- set comprehension notation
    -- def evens : set ℕ := { n : ℕ |isEven n }
      -- let evens be the set of natural numbers, b, 
      of type ℕ, such that n is even
      -- def evens' := { n : ℕ |isEven n }
    -- set comphrehension notation is just 
    notation for the set memberships predicate

  -- membership predicates
    -- sets are literally equivalent to membership predicates

  -- set operations and notations
    - membership, ∈ 
      -- to assert that a value is in a set

    - intersection, ∩ 
      -- satisfies both of the predicates
      -- "x is in A and x is in B"
      -- A x ∧ B x

    - union, ∪ 
      -- satisfies at least one of the predicates
      -- "x is in A or x is in B"
      -- A x ∨ B x

    - complement, ᶜ
      -- everything of the same kind that is not in the set
      -- "x is not in A"
      -- ¬ A x

    - difference, \
      -- everything of the same kind that is in A but not in B
      -- "x is in A but not in B"
      -- A x ∧ ¬ B x

    - subset relation, ⊆, ⊂ 
      -- Equal subsets
        -- When both A and B are subsets of each other
      -- Proper Subset = ⊆
        -- Not subsets of each other
        -- ∀ A, x ∈ A → x ∈ B ∧ ∃x ∈ B → x ∉ A
      -- Strict Subset = ⊂ 
      -- for all elements X, if x is in A, then x is in B
      -- ∀ x, x ∈ A → x ∈ B

    -- powerset 𝒫 (the set of all subsets of a given set)
      -- The set of all subsets of a given set
        -- inlcudes the Null Set
        -- 2ⁿ, n = number of elements
          -- induction
            -- property of set a, is that |𝒫 A| = 2ᴬ 
            -- proposition ∀ n, |A| = n → |𝒫 A| = 2ⁿ
            -- induction 
              -- show that property 1 is true for n = 0
                -- Q 0
              -- show that if property 1 is true for n, then it is true for n + 1
                -- ∀ n', Q n' → Q^(n' + 1)
      -- 𝒫 A = { B | B ⊆ A }

  -- propositions and proofs
-/

/-
  - relations
  -- membership predicates (on pairs of values)
    -- a set of pairs defined by a membership predicate
    -- a relation is a set of pairs
    -- cannot compute with predicates, only prove them
    -- relate objects of different types types

  -- domain, domain of definition, co-domain, range
    -- domain
      -- set a
    -- co-domain
      -- set b
    -- domain of definition
      -- subset of a
    -- range
      -- subset of b
      -- equal to the codomain 
-/

/-
  -- properties of relations
    - reflexivity
      -- **every element** in the domain is related to itself
      -- ∀ x, x ∈ A → r x x
    - symmetry
      -- for all a and b, **if** a is related to b, then b is related to a
        -- not every element
      -- ∀ x, ∀ y, r x y → r y x
    - transitivity
      -- for all a, b, and c, **if** a is related to b and b is related to c, then a is related to c
        -- not every element
      -- ∀ x, ∀ y, ∀ z, r x y ∧ r y z → r x z
    - equivalence
      -- def equivalence := reflexive r ∧ symmetric r ∧ transitive r
      -- a binary relation of type α → α → Prop
      -- eq x y
        -- x = y
      -- eq.refl
        -- introduction rule
        -- every object of given type is equal to itself
      -- eq.subst
        -- elimination rule
        -- if you know that x = y and you have a proof of P y, then you can prove P x
    - asymmetry
    - anti-symmetry
-/

/-
  -- properties of functions
    -- functions map sets of objects to other sets of objects
      -- functions are always one-to-one, many-to-one

    -- injectivity
      -- one-to-one
      -- r a x ∧ r b x → a = b
        -- total function
          -- it is defined for every element in the domain
            -- every α has a β
          -- def total_function := 
              function r → ∀ (a : α), ∃ (b : β), r a b 
        -- partial function
          -- it is not defined for every element in the domain
            -- not every α has a β
          -- def partial_function := 
              function r ∧ ¬ total_function r
    
    -- surjectivity
      -- onto
      -- ∀ b, ∃ a, r a b
        -- every element of the output set has a corresponding element in the input set


    -- bijectivity
      -- onto and one-to-one
        -- def bijective := injective r ∧ surjective r

    -- single-valuedness (functionality)
      -- I cannot have an element in the domain that has two outputs
      -- r x y ∧ r x z → y = z
-/

/-
  - induction
    -- inductive data definitions
      -- every inductively defined data type comes with its own induction axiom
      -- if a type is named T, then the induction axiom is named T.rec_on
      -- an indution axiom is an axiom for proving universal generalizations
        -- something that is true for all values of a given type
      -- f a type has only enumerate values, induction axiom = case analysis
      -- if a type is recursive, then the induction axiom is more complex
        1) show that each base vlaye has the given property
        2) for each constructor show that if you apply it to smaller values that have the given property, then the larger ones you construct will have that property too
      -- proofs by induction
        -- two cases
          1) base case, zero
          2) the inductive case, n + 1, for any n'
            -- assume that the property is true for n'
            -- show that it is true for n' + 1  

    -- induction axioms (for enumerated types and ℕ)
      -- use the "induction" tactic not the "apply" tactic
      -- for enumerated types
        -- we can build proof that all values of this proof have a given property
          -- we apply the induction axiom to smaller machines each of which gives a proof for the corresponding bool input value
        -- we can build a function that taks any value of this type and returns a corresponding result value
          -- we apply the induction axiom to the return values for all possible argument values

    -- definition of recursive functions
      -- We use succ to define the successor function
        -- succ n = n + 1
        -- for addition
          - def my_add : ℕ → ℕ → ℕ 
            | n 0 := n
            | n (succ m') := succ (my_add n m')
          -- we add 1 to n "m times"

    -- construction of proofs by induction
-/

inductive day
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day

def next_day : day → day
| day.monday := day.tuesday
| day.tuesday := day.wednesday
| day.wednesday := day.thursday
| day.thursday := day.friday
| day.friday := day.saturday
| day.saturday := day.sunday
| day.sunday := day.monday

def prev_day : day → day
| day.monday := day.sunday
| day.tuesday := day.monday
| day.wednesday := day.tuesday
| day.thursday := day.wednesday
| day.friday := day.thursday
| day.saturday := day.friday
| day.sunday := day.saturday

example : 
  ∀ d : day, 
  next_day (prev_day d) = d 
  :=
begin
  assume d,
  cases d,
  case day.monday {
    refl,
  }, 
  case day.tuesday {
    refl,
  },
  case day.wednesday {
    refl,
  },
  case day.thursday {
    refl,
  },
  case day.friday {
    refl,
  },
  case day.saturday {
    refl,
  },
  case day.sunday {
    refl,
  },
end