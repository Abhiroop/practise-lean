import Mathlib.Data.Int.Basic

set_option autoImplicit false

namespace Chap3

theorem fst_of_two_props :
  ∀ a b : Prop, a → b → a := by
    intro a b
    intro ha
    intro hb
    apply ha

theorem prop_comp :
  ∀  a b c : Prop, (a → b) → (b → c) → a → c := by
    intro a b c
    intro hab hbc
    intro ha
    apply hbc
    apply hab
    apply ha

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    . cases hab with
      | intro ha hb => apply hb
    . cases hab with
      | intro ha hb => apply ha


theorem And_swap' (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

theorem f5_if (f : ℕ → ℕ) (h : ∀ n : ℕ, f n = n) :
    f 5 = 5 :=
  by exact h 5

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  by
    intro hab
    apply hab

def double (n : ℕ) : ℕ :=
  n + n

theorem Exists_double_iden :
    ∃ n : ℕ, double n = n :=
  by
    apply Exists.intro 0
    rfl

theorem Eq_trans_symm {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    apply Eq.trans
    . apply hab
    . apply Eq.symm
      apply hcb

theorem Eq_trans_symm' {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    rw [hab, hcb]

def add : ℕ → ℕ → ℕ
  | m, Nat.zero => m
  | m, Nat.succ n => Nat.succ (add m n)

theorem add_zero (n : ℕ) :
    add 0 n = n :=
  by
    induction n with
    | zero => rfl
    | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero => rfl
    | succ n' ih => simp [add, ih]
theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

instance Associative_add : Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add : Std.Commutative add :=
  { comm := add_comm }

def mul : ℕ → ℕ → ℕ
| _, Nat.zero => Nat.zero
| m, Nat.succ n => add m (mul m n)

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      ac_rfl



end Chap3
