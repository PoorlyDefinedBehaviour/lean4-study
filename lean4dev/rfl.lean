example : 5 = 5 := rfl
example : "hello" = "hello" := rfl
example : [1,2,3] = [1,2,3] := rfl

example : true = true := rfl
example : () = () := rfl

example : 2 + 2 = 4 := rfl
example : 10 - 3 = 7 := rfl
example : 2 * 3 + 1 = 7 := rfl

example : "hel" ++ "lo" = "hello" := rfl

example : [1,2] ++ [3] = [1,2,3] := rfl
example : [1,2,3].head? = some 1 := rfl

example : (λx ↦ x + 1) 5 = 6 := rfl
example : [1,2,3].length = 3 := rfl
example : (if true then 1 else 2) = 1 := rfl

def double (n : Nat) : Nat := n * 2
example : double 5 = 10 := rfl

def isZero : Nat → Bool
  | 0 => true
  | _ => false

example : isZero 0 = true := rfl
example : isZero 7 = false := rfl

example (n : Nat) : n + 0 = n := rfl

example (n : Nat) : n + 0 = n := by simp
example (n : Nat) : n + 0 = n := Nat.add_zero n

-- Fails
-- example (xs : List Nat ) : xs ++ [] = xs := rfl
example (xs : List Nat) : xs ++ [] = xs := by simp

-- Fails
-- example (n : Nat) : 0 + n = n := rfl
example (n : Nat) : n + 0 = n := rfl

-- Direct proof term
example : 2 + 2 = 4 := rfl

-- As a tactic
example : 2 + 2 = 4 := by rfl

example : 2 + 2 = 4 := by
  show 4 = 4
  rfl

example : 5 = 5 := rfl
example : 5 = 5 := Eq.refl 5
example : 5 = 5 := @rfl Nat 5

#check Eq.refl
#check @Eq.refl

example : ([] : List Nat) = [] := @rfl (List Nat) []

def Config := List (String × Nat)

def defaultConfig : Config := [("timeout", 30), ("retries", 3)]

example : defaultConfig.length = 2 := rfl
example : (defaultConfig.lookup "timeout") = some 30 := rfl

def parseDigit : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | _ => none

example : parseDigit '1' = some 1 := rfl
example : parseDigit 'a' = none := rfl

example (a b : Nat) (h : a = b) : b = a := by
  rw [h] -- Goal becomes b = b

example (x y z : Nat) (h1 : x = y) (h2 : y = z) : x = z := by
  rw [h1] -- replace x with y
  rw [h2] -- replace y with z
  -- z = z

example : 123456 + 789012 = 912468 := by native_decide

example : (3 * 4) + 2 = 14 := rfl

def greet (name : String) : String := "Hello, " ++ name ++ "!"

example : greet "World" = "Hello, World!" := rfl

example (n : Nat) : n + 0 = n := rfl
example (n : Nat) : n + 0 = n := by simp
