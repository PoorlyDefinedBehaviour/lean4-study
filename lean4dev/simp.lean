example (n : Nat) : n + 0 + 0 + 0 = n := by
  simp

example (a b c : Nat) : a + b + c + 0 = c + (b + a) := by
  simp [Nat.add_comm, Nat.add_assoc]

example : [1, 2] ++ [] ++ [3] = [1, 2, 3] := by simp

example (xs : List Nat) : xs ++ [] = xs := by simp

example (n : Nat) : 0 + n = n := by simp

#check @Nat.add_zero
#check @List.append_nil
#check List.append_nil

example (n : Nat) : n + 0 = n := by simp
example (xs : List Nat) : xs ++ [] = xs := by simp
example (b : Bool) : ¬¬b = b := by simp

example (a b : Nat) (h : a = 5) : a + b = 5 + b := by simp [h]

example (f : Nat → Nat) (hf : ∀ n, f n = n + 1) : f 5 = 6 := by simp [hf]

example (a b : Nat) (h1 : a = 0) (h2 : b = 0) : a + b = 0 := by simp [h1, h2]

def triple (n : Nat) := 3 * n

example : triple 4 = 12 := by simp [triple]

example (n : Nat) : n + 0 + 0 = n := by simp only [Nat.add_zero]

example (a b : Nat) (h : a = b) : a + 0 = b := by simp only [Nat.add_zero, h]

example (n : Nat) : n + 0 = n := by simp only [Nat.add_zero]

-- Fails
-- example (a b c : Nat) : a * (b + c) = a * b + a * c := by simp

-- Use ring for algebraic identitites
-- example (a b c : Nat) : a * (b + c) = a * b + a * c := by ring

example (a b c : Nat) : a * (b + c) = a * b + a * c := by rw [Nat.mul_add]

example (a b c : Nat) (h : a = b) : a + c = b + c := by simp only [h]

example (a b : Nat) (h1 : a = 5) (h2 : b = 3) : a + b = 8 := by
  -- Use all hypotheses as simp rules
  simp_all

example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  exact h

example (a b : Nat) (h1 : a + 0 = b) (h2 : b + 0 = 5) : a = 5 := by
  -- Simplifies all hypotheses and the goal
  simp at *
  rw [h1, h2]

example (a b : Nat) (h1 : a + 0 = 3) (h2 : b = 4) : a + b = 7 := by
  simp at h1
  simp [h1, h2]

example (n : Nat) : n + 0 = n := by simp
example (xs : List Nat) : xs ++ [] = xs := by simp

example (a : Nat) (h : a = 5) : a + 0 = 5 := by simp [h]

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by simp_all

example (a b : Nat) (h : a = b) (hb : b = 0) : a = 0 := by simp_all

example (n : Nat) : n + 0 = n := by simp only [Nat.add_zero]

example (a : Nat) (h : a = 5) : a + 0 = 5 := by simp only [h, Nat.add_zero]

example (n : Nat) : n + 1 - 1 = n := by simp_arith

example (a b : Nat) : a + b + 1 = 1 + a + b := by simp_arith

example (n : Nat) : (n + 0) + 1 -1 = n := by simp_arith

def myConst := 42
example : myConst = 42 := by dsimp [myConst]

example : (let x := 5; x + x) = 10 := by
  dsimp only

example (n : Nat) : n + 0 = n := by dsimp

def double (n : Nat) : Nat := n + n

@[simp]
theorem double_zero : double 0 = 0 := rfl

-- @[simp]
-- theorem double_succ (n : Nat) : double (n + 1) = double n + 2 := by
--   simp [double]
--   -- need to import mathlib
--   ring

example : double 0 + double 0 = 0 := by simp
-- example : double 1 = 2 := by simp

example (a b c : Nat) : a + (b + c) = (a + b) + c := by
  -- ring
  -- or
  -- rw [Nat.add_assoc]
  -- or
  omega
  -- or
  -- linarith

example (n : Nat) (h : n > 5) : n > 3 := by omega

example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by rw [h]

example (b : Bool) : b ∨ true = true := by cases b <;> simp

example (xs : List Nat) : [] ++ xs ++ [] = xs := by simp

example (n : Nat) (h : n = 3) : n + 0 = 3 := by
  simp [h]

example (a b : Nat) : a + 0 + b + 0 = a + b := by
  simp only [Nat.add_zero]
