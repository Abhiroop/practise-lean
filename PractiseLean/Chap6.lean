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

inductive Sorted : List ℕ → Prop where
| nil : Sorted []
| single (x : ℕ) : Sorted [x]
| two_or_more (x y : ℕ) {zs : List ℕ} (hle : x ≤ y)
      (hsorted : Sorted (y :: zs)) :
  Sorted (x :: y :: zs)

theorem Sorted_3_5 :
    Sorted [3, 5] :=
  Sorted.two_or_more _ _ (by simp) (Sorted.single _)

theorem Not_Sorted_17_13 :
    ¬ Sorted [17, 13] :=
  by
    intro h
    cases h with
    | two_or_more _ _ hlet hsorted => omega


#check absurd

theorem Not_Even_two_mul_add_one (m n : ℕ)
    (hm : m = 2 * n + 1) :
  ¬ Even m := by
  intro hn
  induction hn generalizing n with
  | zero => omega
  | add_two k a ih => apply ih (n - 1)
                      omega



end Chap6
