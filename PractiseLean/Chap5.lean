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

theorem map_comp {α β γ : Type} (f : α → β) (g : β → γ)
    (xs : List α) :
  map g (map f xs) = map (fun x ↦ g (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [map, ih]

def headPre {α : Type} : (xs : List α) → xs ≠ [] → α
  | [], hxs => by simp at *
  | x :: _, hxs => x

def zip {α β : Type} : List α → List β → List (α × β)
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | [], _ => []
  | _ :: _, [] => []

def length {α : Type} : List α → ℕ
  | [] => 0
  | x :: xs => length xs + 1

theorem length_zip {α β : Type} (xs : List α) (ys : List β) :
    length (zip xs ys) = min (length xs) (length ys) :=
  by
    induction xs generalizing ys with
    | nil => simp [zip, length]
    | cons x xs ih =>
                      cases ys with
                      | nil => simp [zip, length]
                      | cons y ys' => simp [zip, length, ih]; omega


inductive Vec (α : Type) : ℕ  → Type where
  | nil : Vec α 0
  | cons (a : α) {n : ℕ} (v : Vec α n) : Vec α (n + 1)

end Chap5
