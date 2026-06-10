-- This module serves as the root of the `PractiseLean` library.
-- Import modules here that should be built as part of the library.
import PractiseLean.Basic
import Init.Prelude

universe u v w

#eval 1 + 2
#eval 1 + 2 * 5
#eval String.append "Hello, " "Lean!"
#eval if 3 == 4 then "equal" else "not equal"
#check (1 - 2 : Int)


def lean : String := "Lean"
def add1 (n : Nat) : Nat := n + 1
#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n

def Str : Type := String

structure Point where
  x : Float
  y : Float
deriving Repr -- like deriving Show

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin
#eval origin.x

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

-- mutating a field
def zeroX (p : Point) : Point :=
  { p with x := 0 }

inductive Bool1 where
  | false : Bool1
  | true : Bool1

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false
