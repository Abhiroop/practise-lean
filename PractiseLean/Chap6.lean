import Mathlib.Data.Int.Basic
import PractiseLean.LoveLib
set_option autoImplicit false

namespace Chap6

inductive Even : ℕ → Prop where
| zero: Even 0
| add_two : ∀k : ℕ, Even k → Even (k + 2)

theorem Even_4 :
  Even 4 := .add_two _ (.add_two _ .zero)


end Chap6
