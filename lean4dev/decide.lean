#check @Decidable
#check Decidable

#check (inferInstance : Decidable (2 + 2 = 4))

example : 2 + 2 = 4 := by decide
example : 17 ≠ 18 := by decide

example : true ∧ true := by decide
example : ¬false := by decide

example : [1,2,3].length = 3 := by decide
example : [1,2,3].contains 2 = true := by decide

example : 2 + 2 = 4 := rfl
example : 2 + 2 = 4 := by decide

example : ¬(3 = 5) := by decide
-- rfl can't handle it
-- example : ¬(3 = 5) := rfl

example : 1 < 2 := by decide

example : 3 ∈ [1,2,3,4] := by decide

example : (List.range 1000).length = 1000 := by native_decide

-- example : Nat.Prime 97 := by native_decide

structure Person where
  name : String
  age : Nat
deriving DecidableEq

example : (Person.mk "Alice" 30) = (Person.mk "Alice" 30) := by decide

inductive Color
  | red
  | green
  | blue
deriving DecidableEq

example : Color.red ≠ Color.blue := by decide

def isEven (n : Nat) : Prop := n % 2 = 0

instance (n : Nat) : Decidable (isEven n) :=
  if h : n % 2 = 0 then isTrue h else isFalse h

example : isEven 4 := by decide
example : ¬isEven 5 := by decide
