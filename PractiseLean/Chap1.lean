import Mathlib.Data.Int.Basic

set_option autoImplicit false

namespace Chap1

theorem one_plus_one : 1 + 1 = 2 := by
  rfl

theorem add_comm_simple (n : Nat) : n + 0 = n := by
  rfl

theorem add_zero (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [ih]

opaque a : ℤ
opaque b : ℤ
opaque f : ℤ → ℤ
opaque g : ℤ → ℤ → ℤ
#check fun x : ℤ ↦ g (f (g a x)) (g x b)
#check fun x ↦ g (f (g a x)) (g x b)

end Chap1
