theorem
and_commutes:
∀ (P Q : Prop), P ∧ Q → Q ∧ P
:=
begin
  intros P Q,
  assume h : P ∧ Q,
  let p := and.elim_left h,
  let q := and.elim_right h,
  apply and.intro q p, 
end

/-
Theorem: Logical and is communitive. #check

Proof: Assume P and Q are arbitrary but specific propositions, 
and that we have a proof P ∧ Q. From this proof we can derive proofs of P and of Q seperately. 
Then we can combine these proofs in the opposite order to construt a proof of Q ∧ P.
-/