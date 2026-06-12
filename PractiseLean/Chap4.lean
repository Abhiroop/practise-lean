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


#check And.intro
#check Exists.intro

theorem Exists.one_point {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (fun hex => Exists.elim hex (fun x hxp =>
                                  let heq := And.left  hxp
                                  let hpx := And.right hxp
                                  heq ▸ hpx))
    (fun pt => Exists.intro t (And.intro rfl pt))

theorem Exists.one_point' {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume hex : ∃ x, x = t ∧ P x
     show P t from
      Exists.elim hex
        (fix x : α
         assume hand : x = t ∧ P x
         have hxt : x = t :=
          And.left hand
         have hpx : P x :=
          And.right hand
         show P t from
          by
            rw [←hxt]
            exact hpx)
    )
    (assume pt : P t
     show ∃ x, x = t ∧ P x from
     Exists.intro t
      (have tt : t = t :=
        by rfl
        show t = t ∧ P t from
          And.intro tt pt))

#check Nat.two_mul

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m :=
  calc
    2 * m + n = m + m + n :=
      by rw [Nat.two_mul]
    _ = m + n + m :=
      by ac_rfl

def reverse {α : Type} : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

#check Eq
#check List.append_nil

theorem reverse_append {α : Type} :
  ∀ xs ys : List α,
    reverse (xs ++ ys) = reverse ys ++ reverse xs := by
  intro xs
  induction xs with
  | nil => intro ys
           simp
           rfl
  | cons x xs ih => intro ys
                    simp [reverse]
                    rw [ih, List.append_assoc]

theorem reverse_reverse {α : Type} :
  ∀ xs : List α,
    reverse (reverse xs) = xs := by
  intro xs
  induction xs with
  | nil => simp [reverse]
  | cons x xs ih => simp [reverse]
                    rw [reverse_append, ih]
                    simp [reverse]

theorem reverse_reverse' {α : Type} :
  ∀ xs : List α,
    reverse (reverse xs) = xs
  | [] => by rfl
  | x :: xs => by
                  simp [reverse]
                  rw [reverse_append, reverse_reverse']
                  simp [reverse]



end Chap4
