import Mathlib.Data.Int.Basic
import PractiseLean.LoveLib
set_option autoImplicit false

namespace Chap5


#check Nat.succ.inj

theorem Nat.succ_neq_self (n : ℕ ) :
    Nat.succ n ≠ n :=
  by
    induction n with
    | zero => simp
    | succ n' ih => simp


def head {α : Type} [Inhabited α] : List α → α
  | [] => Inhabited.default
  | x :: _ => x

theorem head_head_cases {α : Type} [Inhabited α]
    (xs : List α) :
  head [head xs] = head xs :=
  by
    cases xs with
    | nil => rfl
    | cons x xs => rfl

theorem injection_example {α : Type} (x y : α) (xs ys : List α)
    (h : x :: xs = y :: ys) :
  x = y ∧ xs = ys :=
  And.intro
  (by
     cases h
     rfl)
  (by
    cases h
    rfl)

def map {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs

theorem map_ident {α : Type} (xs : List α) :
  map (fun x ↦ x) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [map, ih]

end Chap5
