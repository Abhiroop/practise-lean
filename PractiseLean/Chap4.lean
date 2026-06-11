import Mathlib.Data.Int.Basic
import PractiseLean.LoveLib
set_option autoImplicit false

namespace Chap4

theorem fst_of_two_props :
    ∀ a b : Prop, a → b → a :=
  fix a b : Prop
  assume ha : a
  assume hb : b
  show a from
    ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  assume ha : a
  have hb : b :=
    hab ha
  have hc : c :=
    hbc hb
  show c from
    hc

theorem modus_ponens :
    ∀ a b : Prop, a → (a → b) → b :=
  fix a b : Prop
  assume ha : a
  assume hab : a → b
  have hb : b :=
    hab ha
  show b from
    hb

theorem prop_comp_inline (a b c : Prop) (hab : a → b)
    (hbc : b → c) :
  a → c :=
  assume ha : a
  show c from
    hbc (hab ha)

theorem two_add_two_Eq_four :
    2 + 2 = 4 := rfl

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  assume hab : a ∧ b
  have ha : a :=
    And.left hab
  have hb : b :=
    And.right hab
  show b ∧ a from
    And.intro hb ha

theorem And_swap' (a b : Prop) :
    a ∧ b → b ∧ a :=
  fun (hab : a ∧ b) =>
    And.intro (And.right hab) (And.left hab)

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
    (∀x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume hall : (∀ (x : α), x = t → P x)
     show P t from
      by
        apply hall t
        rfl
    )
    (assume hp : P t
     fix x : α
     assume heq : x = t
     show P x from
      by
        rw [heq]
        exact hp)

theorem beast_666 (beast : ℕ) :
    (∀n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
  Forall.one_point _ _

theorem Forall.one_point' {α : Type} (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (fun hall => hall t rfl)
    (fun hp => fun _ => fun heq => heq ▸ hp)

theorem Exists.one_point {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t ∧ P x) ↔ P t :=
  sorry

end Chap4
