import Mathlib.Data.Int.Basic
import PractiseLean.LoveLib
set_option autoImplicit false

namespace Chap6

inductive Even : ℕ → Prop where
| zero: Even 0
| add_two : ∀k : ℕ, Even k → Even (k + 2)

theorem Even_4 :
  Even 4 := .add_two _ (.add_two _ .zero)

#check Or.inl
#check Exists.intro

theorem Even_Iff_struct (n : ℕ) :
    Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  Iff.intro
    ( assume hn : Even n
      match hn with
      | Even.zero =>
        show 0 = 0 ∨ _ from
          Or.inl rfl
      | Even.add_two k hk =>
        show _ ∨ ∃ m, k + 2 = m + 2 ∧ Even m from
          Or.inr (Exists.intro k (And.intro rfl hk))
    )
    (assume hr : (n = 0 ∨ ∃ m, n = m + 2 ∧ Even m)
     match hr with
     | Or.inl heq => heq ▸ Even.zero
     | Or.inr hex =>
        match hex with
        | ⟨ m, hand ⟩ =>
          match hand with
          | ⟨heq, heven ⟩ =>
            show Even n from
              have mplustwo : Even (m + 2) :=
                Even.add_two m heven
              heq ▸ mplustwo
    )

end Chap6
