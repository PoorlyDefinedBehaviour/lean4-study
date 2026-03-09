def absolute (x : Int) : Int :=
  if x < 0 then -x else x

#eval absolute (-5)
#eval absolute 3

def classifyNumber (n : Int) : String :=
  if n < 0 then "negative"
  else if n == 0 then "zero"
  else "positive"

#eval classifyNumber (-10)
#eval classifyNumber 0
#eval classifyNumber 42

def minValue (a b : Nat) : Nat :=
  if a < b then a else b

#eval minValue 3 7

def describeList {α : Type} (xs : List α) : String :=
  match xs with
  | [] => "empty"
  | [_] => "singleton"
  | [_, _] => "pair"
  | _ => "many elements"

def fizzbuzz (n : Nat) : String :=
  match n % 3, n % 5 with
  | 0, 0 => "FizzBuzz"
  | 0, _ => "Fizz"
  | _, 0 => "Buzz"
  | _, _ => toString n

#eval (List.range 16).map fizzbuzz

def classifyAge (age : Nat) : String :=
  match age with
  | 0 => "infant"
  | n => if n < 3 then "child"
         else if n < 20 then "teenager"
         else "adult"

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

def length {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + length xs

def factorialTR (n : Nat) : Nat :=
  let rec go (acc : Nat) : Nat → Nat
    | 0 => acc
    | k + 1 => go (acc * (k + 1)) k
  go 1 n

def sumTR (xs : List Nat) : Nat :=
  let rec go (acc : Nat) : List Nat → Nat
    | [] => acc
    | x :: rest => go (acc + x) rest
  go 0 xs

def reverseTR {α : Type} (xs : List α) : List α :=
  let rec go (acc : List α) : List α → List α
    | [] => acc
    | x :: rest => go (x :: acc) rest
  go [] xs

def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys

def mergeSort (xs : List Nat) : List Nat :=
  if h : xs.length < 2 then xs
  else
    let mid := xs.length / 2
    let left := xs.take mid
    let right := xs.drop mid
    have hl : left.length < xs.length := by
      have h1 : mid < xs.length := Nat.div_lt_self (by omega) (by omega)
      have h2 : left.length ≤ mid := List.length_take_le mid xs
      omega
    have hr : right.length < xs.length := by
      simp only [List.length_drop, right, mid]
      have : mid > 0 := Nat.div_pos (by omega) (by omega)
      omega
    merge (mergeSort left) (mergeSort right)
termination_by xs.length

partial def findFixpoint (f : Nat → Nat) (x : Nat) : Nat :=
  let y := f x
  if y == x then x else findFixpoint f y

partial def sumEvensFibsBelow (bound : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  let mut sum := 0
  while b < bound do
    if b % 2 == 0 then
      sum := sum + b
    let next := a + b
    a := b
    b := next
  return sum

def validatePositive (n : Int) : IO (Option Int) := do
  unless n > 0 do
    return none
  return some n

def processIfValid (values : List Nat) : IO Unit := do
  for v in values do
    unless v >= 0 do
      continue
    IO.println s!"Processing: {v}"

def sumList (xs : List Nat) : Nat := Id.run do
  let mut total := 0
  for x in xs do
    total := total + x
  return total

def sumRange (n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in [0:n] do
    total := total + i
  return total

def sumEvens (n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in [0:n:2] do
    total := total + i
  return total

def findMax (arr : Array Int) : Option Int := Id.run do
  if arr.isEmpty then return none
  let mut maxVal := arr[0]!
  for x in arr do
    if x > maxVal then maxVal := x
  return some maxVal

def countdownFrom (n : Nat) : List Nat := Id.run do
  let mut result : List Nat := []
  let mut i := n
  while i > 0 do
    result := i :: result
    i := i - 1
  return result.reverse

def gcd (a b : Nat) : Nat := Id.run do
  let mut x := a
  let mut y := b
  while y != 0 do
    let temp := y
    y := x % y
    x := temp
  return x

def findFirst (xs : List Nat) (pred : Nat → Bool) : Option Nat := Id.run do
  for x in xs do
    if pred x then return some x
  return none

def sumPositives (xs : List Int) : Int := Id.run do
  let mut total : Int := 0
  for x in xs do
    if x <= 0 then continue
    total := total + x
  return total

def findInMatrix (m : List (List Nat)) (target : Nat) : Option (Nat × Nat) := Id.run do
  let mut i := 0
  for row in m do
    let mut j := 0
    for val in row do
      if val == target then return some (i, j)
      j := j + 1
    i := i + 1
  return none

def imperative_factorial (n : Nat) : Nat := Id.run do
  let mut result := 1
  let mut i := n
  while i > 0 do
    result := result * i
    i := i -1
  return result

def fibPair (n : Nat) : Nat × Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [0:n] do
    let temp := a + b
    a := b
    b := temp
  return (a, b)

def buildReversed {α : Type} (xs : List α) : List α := Id.run do
  let mut result : List α := []
  for x in xs do
    result := x :: result
  return result

def demonstrate_assignment : Nat := Id.run do
  let mut x := 10
  x := x + 5
  x := x * 2
  return x

#print demonstrate_assignment
#reduce demonstrate_assignment
#check demonstrate_assignment

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := {x := 0.0, y := 0.0}
def point1 : Point := Point.mk 3.0 4.0
def point2 : Point := ⟨1.0, 2.0⟩

#eval point1.x
#eval point1.y

def distance (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval distance point1

def moveRight (p : Point) (dx : Float) : Point :=
  {p with x := p.x + dx}

def moveUp (p : Point) (dy : Float) : Point :=
  {p with y := p.y + dy}

def translate (p : Point) (dx dy : Float) : Point :=
  {p with x := p.x + dx, y := p.y + dy}

#eval translate origin 3.0 4.0

structure Rectangle where
  topLeft : Point
  bottomRight : Point
deriving Repr

def myRect : Rectangle :=
  { topLeft := {x := 0.0, y := 10.0}, bottomRight := {x := 10.0, y := 0.0}}

def width (r : Rectangle) : Float :=
  r.bottomRight.x - r.topLeft.x

def height (r : Rectangle) : Float :=
  r.topLeft.y - r.bottomRight.y

def area (r : Rectangle) : Float :=
  width r * height r

#eval area myRect

structure Config where
  host : String := "localhost"
  port : Nat := 8080
  debug : Bool := false
deriving Repr

def defaultConfig : Config := {}

def prodConfig : Config := {host := "api.example.com", port := 443}
#eval defaultConfig
#eval prodConfig

inductive Direction where
  | north
  | south
  | east
  | west
deriving Repr, DecidableEq

def opposite : Direction → Direction
  | .north => .south
  | .south => .north
  | .east => .west
  | .west => .east

inductive StarshipClass where
  | galaxy
  | sovereign
  | defiant
  | intrepid
  | constitution
deriving Repr, DecidableEq

def crewComplement : StarshipClass → Nat
  | .galaxy => 1024
  | .sovereign => 855
  | .defiant => 50
  | .intrepid => 141
  | .constitution => 430

inductive Spell where
  | creature (power : Nat) (toughness : Nat) (manaCost : Nat)
  | instant (manaCost : Nat)
  | sorcery (manatCost : Nat)
  | enchantment (manaCost : Nat) (isAura : Bool)
deriving Repr

def manaCost : Spell → Nat
  | .creature _ _ cost => cost
  | .instant cost => cost
  | .sorcery cost => cost
  | .enchantment cost _ => cost

def canBlock : Spell → Bool
  | .creature _ toughness _ => toughness > 0
  | _ => false

inductive BinaryTree (α : Type) where
  | leaf : BinaryTree α
  | node : α → BinaryTree α → BinaryTree α → BinaryTree α
deriving Repr

def exampleTree : BinaryTree Nat :=
  .node 1
    (.node 2 .leaf .leaf)
    (.node 3
      (.node 4 .leaf .leaf)
      .leaf)

def BinaryTree.size {α : Type} : BinaryTree α → Nat
  | .leaf => 0
  | .node _ left right => 1 + left.size + right.size

def BinaryTree.depth {α : Type} : BinaryTree α → Nat
  | .leaf => 0
  | .node _ left right => 1 + max left.depth right.depth

def BinaryTree.inorder {α : Type} : BinaryTree α → List α
  | .leaf => []
  | .node x left right => left.inorder ++ [x] ++ right.inorder

inductive Expr (α : Type) where
  | lit : α →  Expr α
  | add : Expr α → Expr α → Expr α
  | mul : Expr α → Expr α → Expr α
deriving Repr

def Expr.eval {α : Type} [Add α] [Mul α] : Expr α → α
  | .lit n => n
  | .add e1 e2 => e1.eval + e2.eval
  | .mul e1 e2 => e1.eval * e2.eval

def intExpr : Expr Int := .mul (.add (.lit 2) (.lit 3)) (.lit 4)

def Expr.map {α β : Type} (f : α → β) : Expr α → Expr β
  | .lit n => .lit (f n)
  | .add e1 e2 => .add (e1.map f) (e2.map f)
  | .mul e1 e2 => .mul (e1.map f) (e2.map f)

#eval intExpr.map (λn ↦ Float.ofInt n)

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

mutual
  inductive Tree (α : Type) where
    | node : α → Forest α → Tree α

  inductive Forest (α : Type) where
    | nil : Forest α
    | cons : Tree α → Forest α → Forest α
end
