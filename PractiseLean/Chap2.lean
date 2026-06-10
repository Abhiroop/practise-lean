import Mathlib.Data.Int.Basic

set_option autoImplicit false

namespace Chap2

namespace MyNat

/- Definition of type `Nat` (= `ℕ`) of natural numbers, using unary notation: -/

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

#check Nat
#check Nat.zero
#check Nat.succ

/- `#print` outputs the definition of its argument. -/

#print Nat

end MyNat

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp

namespace MyList

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α

#check List
#check List.nil
#check List.cons
#print List

end MyList


def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

def add : ℕ → ℕ → ℕ
  | m, Nat.zero => m
  | m, Nat.succ n => Nat.succ (add m n)

#eval add 2 7
#reduce add 2 7

def mul : ℕ → ℕ → ℕ
| _, Nat.zero => Nat.zero
| m, Nat.succ n => add m (mul m n)

#eval mul 2 7

def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂

#eval eval (fun _ ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))

def append (α : Type) : List α → List α → List α
  | [], ys      => ys
  | x :: xs, ys => x :: (append α xs ys)


#check append
#eval append ℕ [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]


def appendImplicit {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]

#check @appendImplicit
#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
#eval @appendImplicit _ [3, 1] [4, 1, 5]

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

namespace SorryTheorems

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  sorry

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  sorry

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  sorry

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  sorry

theorem reverse_reverse {α : Type} (xs : List α) :
    reverse (reverse xs) = xs :=
  sorry

/- Axioms are like theorems but without proofs. Opaque declarations are like
definitions but without bodies. -/

opaque a : ℤ
opaque b : ℤ

axiom a_less_b :
    a < b

end SorryTheorems

end Chap2
