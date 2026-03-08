def zero : Nat := 0

#eval zero

def one : Nat := Nat.succ Nat.zero
def two : Nat := Nat.succ (Nat.succ Nat.zero)

#eval one
#eval two

def fortyTwo : Nat := 42

theorem deep_thought : fortyTwo = 6 * 7 := rfl

def myNat : Nat := 42
def anotherNat : Nat := 100

#eval 3 + 5
#eval 3 - 10

def myInt : Int := -17
def posInt : Int := 42

#eval -5 + 3
#eval 3 - 10
#eval (3 : Int) - 10

#eval (42 : Int).toNat
#eval (42 : Int).natAbs
#eval (-42 : Int).natAbs

/-- Documentation comments start with /-- and end with -/
    They attach to the following declaration and support markdown.
    Use these to document your API. -/
def documented (n : Nat) : Nat := n + 1

#check Nat

namespace Geometry2
  structure Point2 where
    x : Float
    y : Float

  def theOrigin : Point2 := ⟨0.0, 0.0⟩

  def dist (p q : Point2) : Float :=
    let dx := p.x - q.x
    let dy := p.y - q.y
    Float.sqrt (dx * dx + dy * dy)

  def explicit : Point2 := Point2.mk 3.0 4.0
  def shorthand : Point2 := ⟨3.0, 4.0⟩
end Geometry2

#eval Geometry2.dist Geometry2.theOrigin ⟨3.0, 4.0⟩

open Geometry2 in
#eval dist theOrigin ⟨3.0, 4.0⟩

section VectorOps
  variable (α : Type) [Add α] [Mul α]

  def doubleIt (x : α) : α := x + x
  def squareIt (x : α) : α  := x * x
end VectorOps

#eval doubleIt Nat 21
#eval squareIt Nat 7

def hypotenuse (a b : Float) : Float :=
  let aSquared := a * a
  let bSquared := b * b
  Float.sqrt (aSquared + bSquared)

def quadraticRoots (a b c : Float) : Float × Float :=
  ((-b + discriminant) / denom, (-b - discriminant) / denom)
where
  discriminant := Float.sqrt (b * b - 4 * a * c)
  denom := 2 * a

def shadowExample : Nat :=
  let x := 1
  let result :=
    let x := 2
    x + 10
  result + x

#eval shadowExample

namespace Internal
  private def helperVal : Nat := 42
  def publicApi : Nat := helperVal * 2
end Internal

#eval Internal.publicApi
-- Not accessible outside this file
#eval Internal.helperVal

namespace Math
  def square (x : Nat) : Nat := x * x
  def cube (x : Nat) : Nat := x * x * x
end Math

namespace Prelude
  -- Re-export square from Math into Prelude
  export Math (square)
end Prelude

#eval Prelude.square 5

def add (x : Nat) (y : Nat) : Nat :=
  x + y

def double : Nat → Nat :=
  fun x ↦ 2 * x

-- Partially applied
def addFive := add 5

#eval add 3 4
#eval double 21
#eval addFive 10

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def describe : Nat → String
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
  | n => s!"many ({n})"

#eval factorial 5
#eval describe 0
#eval describe 100

abbrev NatPair := Nat × Nat
abbrev Predicate' (α : Type) := α → Bool

def isEvenPred : Predicate' Nat := fun x ↦ x % 2 == 0
def sumPair (p : NatPair) : Nat := p.1 + p.2

#eval isEvenPred 4
#eval sumPair (3, 7)

#check @List.map
#check List.map

#reduce (fun x ↦ x + 1) 5
#reduce List.map (· + 1) [1, 2, 3]

def twice (n : Nat) := n * 2
def square (n : Nat) := n * n
def inc (n : Nat) := n + 1

#eval (square ∘ twice) 3
#eval (twice ∘ square) 3
#eval (inc ∘ square ∘ twice) 3

#eval 3 |> twice |> square |> inc
#eval 10 |> twice
#eval [1, 2, 3] |> List.reverse

#eval String.length <| "hello" ++ " world"
#eval List.map twice <| [1, 2, 3]

def processThenSquare := square ∘ twice ∘ inc
#eval processThenSquare 2

#eval [1,2,3].map (· * 2)
#eval [1,2,3].filter (· > 2)
#eval [1,2,3].foldl (· + ·) 100

theorem add_comm_example : 2 + 3 = 3 + 2 := rfl

example : [1,2,3].reverse.reverse = [1,2,3] := rfl
example : [1,2,3].length + [4,5].length = 5 := rfl
example : [1,2,3].map (· + 10) = [11,12,13] := rfl
