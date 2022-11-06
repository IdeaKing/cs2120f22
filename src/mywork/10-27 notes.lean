-- if there is someone everybody loves, then everybody loves someone

example
  (Person : Type)
  (Loves : Person -> Person -> Prop)
  :  
  (∃ (p : Person), ∀(q : Person), Loves p q) → 
  (∀ (p : Person), ∃(q : Person), Loves q p)
  :=

begin
  assume p_loves_everyone,
  assume p,
  cases p_loves_everyone with p' p'_loves_everyone,
  existsi p',
  exact p'_loves_everyone p,
end

/-

  assume h
  acase h
  assume bruce
  apply exists.intro lenny _,
  apply everyone_loves_lenny bruce

-/

/- 
We'll assume there's someone everyone loves. 
By exists ielim, lets call that person lenny. 
We will also now have that everyone loves 
lenny. Now pick an arbitrary person, lets call
him or her bruce. We have to show that there's
someone bruce loves. But everyone loves lenny, 
so bruce loves lenny. QED

-/



def exists_elim := 
  ∀ {X : Type} 
    {P : X → Prop}
    {Y : Prop}, 
    (∃ (x : X), P x) → 
    (∀ (x : X), P x → Y) → 
    Y 

example : exists_elim :=
begin
  unfold exists_elim,
  assume X P Y,
  assume exists_x_with_p,
  assume if_any_x_has_p_then_y,
  cases exists_x_with_p with x px,
  exact if_any_x_has_p_then_y x px,
end

/- 
{} Braces

Polymorphism  
  Identity function on natural numbers

  def id_nat : ℕ → ℕ := 
  | n := n

  example : id_nat 5 = 5 := rfl
-/

def id_string : string → string
| s := s

def id_bool : bool → bool
| b := b

def id_T' : ∀(T : Type), T → T
| T t := t

#eval id_T' nat 3
#eval id_T' string "hello"

def id_T {T : Type} : T → T
| t := t

#eval id_T 3



-- the syntax of predicate logic includes predicate symbols
-- define functions and incorporate into propositions
-- logic to programming
-- logic includes function symbols
-- part of first order and constructive logic includes logic


namespace my_types

inductive empty : Type
inductive unit : Type
| star : unit

def unit_fun : unit → unit
| unit := unit

open unit 

#eval unit_fun star 

inductive bool : Type



end my_types
