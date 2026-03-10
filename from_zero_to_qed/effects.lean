def safeDivide (x y : Nat) : Option Nat :=
  if y == 0 then none else some (x / y)

def safeHead {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: _ => some x

def computation (xs : List Nat) : Option Nat :=
  match safeHead xs with
  | none => none
  | some x =>
    match safeDivide 100 x with
    | none => none
    | some y => some (y + 1)

def computation' (xs : List Nat) : Option Nat :=
  safeHead xs >>= λx ↦
  safeDivide 100 x >>= λy ↦
  some (y + 1)

#eval computation' [5,  2, 3]
#eval computation' [0, 2, 3]

def computationDo (xs : List Nat) : Option Nat := do
  let x ← safeHead xs
  let y ← safeDivide 100 x
  return y + 1

def validateInput (name : String) (age : Nat) : Option (String × Nat) := do
  if name.isEmpty then none
  if age == 0 then none
  return (name, age)

def withBind (xs : List Nat) : Option Nat :=
  safeHead xs >>= λx ↦
  safeDivide 100 x >>= λy ↦
  pure (y + 1)

def withDoNotation (xs : List Nat) : Option Nat := do
  let x ← safeHead xs
  let y ← safeDivide 100 x
  return y + 1

def mixedBindings : Option Nat := do
  let x ← some 10
  let y := x + 5
  let z ← some (y * 2)
  return z

def imperativeSum (xs : List Nat) : Nat := Id.run do
  let mut total := 0
  for x in xs do
    total := total + x
  return total

def functionalSum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

def countValid (xs : List Nat) : IO Nat := do
  let mut count := 0
  for x in xs do
    if x > 0 then
      count := count + 1
      IO.println s!"Valid: {x}"
  return count

inductive ValidationError where
  | emptyName
  | invalidAge (age : Nat)
  | missingField (field : String)
deriving Repr

def validateName (name : String) : Except ValidationError String :=
  if name.isEmpty then .error .emptyName
  else .ok name

def validateAge (age : Nat) : Except ValidationError Nat :=
  if age == 0 ∨ age > 150 then .error (.invalidAge age)
  else .ok age

def validatePerson (name : String) (age : Nat) : Except ValidationError (String × Nat) := do
  let validName ← validateName name
  let validAge ← validateAge age
  return (validName, validAge)

abbrev Rollback := StateT Nat (Except Unit)

abbrev Audit := ExceptT Unit (StateM Nat)

def countThenFailRollback : Rollback Unit := do
  modify (· + 1)
  modify (· + 1)
  throw  ()
  modify (· + 1)

#eval StateT.run countThenFailRollback 0

def countThenFailAudit : Audit Unit := do
  modify (· + 1)
  modify (· + 1)
  throw ()
  modify (· + 1)

#eval StateT.run (ExceptT.run countThenFailAudit) 0

namespace ManualState

abbrev State (σ α : Type) := σ → (α × σ)

def get {σ : Type} : State σ σ := λs ↦ (s , s)

def set {σ : Type} (newState : σ) : State σ Unit := λ_ ↦ ((), newState)

def modify {σ : Type} (f : σ → σ) : State σ Unit := λs ↦ ((), f s)

def run {σ α : Type} (init : σ) (m : State σ α) : α × σ :=
  m init

def counter : State Nat Nat := λn ↦ (n, n +1)

#eval run 0 counter
#eval run 10 counter

end ManualState

def tick : StateM Nat Unit := modify (· + 1)

def getTicks : StateM Nat Nat := get

def countOperations : StateM Nat Nat := do
  tick
  tick
  tick
  let count ← getTicks
  return count

#eval countOperations.run 0
#eval countOperations.run 10

def pairs (xs : List Nat) (ys : List Nat) : List (Nat × Nat) :=
  xs.flatMap λx ↦ ys.map λy ↦ (x, y)

#eval pairs [1,2] [10,20]


def pythatTriples (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap λa ↦
  (List.range n).flatMap λb ↦
  (List.range n).filterMap λc ↦
    if a * a + b * b == c * c ∧ a > 0 ∧ b > 0 then
      some (a, b, c)
    else none

#eval pythatTriples 15

structure CountDown where
  start : Nat

instance : ForIn Id CountDown Nat where
  forIn cd init f := do
    let mut acc := init
    let mut i := cd.start
    while i > 0 do
      match ← f i acc with
      | .done a => return a
      | .yield a => acc := a
      i := i -1
    return acc

def sumCountDown (n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in CountDown.mk n do
    total := total + i
  return total

#eval sumCountDown 5

def printAll (xs : List String) : IO Unit := do
  for x in xs do
    IO.println x

def sumWithIndex (arr : Array Nat) : Nat := Id.run do
  let mut total := 0
  for h: i in [0:arr.size] do
    total := total + arr[i]
  return total

def manualForIn (xs : List Nat) : Option Nat :=
  ForIn.forIn xs 0 λx acc ↦
    if x == 0 then some (.done acc)
    else some (.yield (acc + x))
