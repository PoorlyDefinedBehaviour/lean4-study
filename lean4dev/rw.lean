example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
  -- Goal was: a + 1 = b + 1
  -- After rw : b + 1 = b + 1

example (x y : Nat) (h : x = y) : x * x = y * y := by
  rw [h]
  -- Goal was: x * x = y * y
  -- After rw: y * y = y * y

example (a b : Nat) (h : a = b) : b = a := by
  rw [← h]

example (a b : Nat) (h : a = b) : b + 1 = a + 1 := by
  rw [← h]
  -- Goal becomes a + 1 = a + 1

example (x y : Nat) (h : x = y + 1) : y + 1 = x := by
  rw [← h]
  -- Goal becomes y + 1 = y + 1

example (n : Nat) : n + 0 = n := by
  rw [Nat.add_zero]

example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]

example (n : Nat) : 0 + n = n := by
  rw [Nat.zero_add]

example (a b c : Nat) : (a + b) + c = a + (b + c) := by
  rw [Nat.add_assoc]

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

example (n : Nat) : n + 0 + 0 = n := by
  rw [Nat.add_zero, Nat.add_zero]

example (a b : Nat) : (a + 0) + b = b + a := by
  rw [Nat.add_zero, Nat.add_comm]

example (a b : Nat) (h1 : a = b) (h2 : a + 1 = 5) : b + 1 = 5 := by
  rw [h1] at h2
  exact h2

example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  rw [Nat.add_zero] at h
  exact h

example (a b : Nat) (h : a = b) (h1 : a > 0) (h2 : a < 10) : b > 0 ∧ b < 10 := by
  rw [h] at h1 h2
  exact ⟨h1, h2⟩

example (a b : Nat) (h : a = b) (h2 : a + a = 10) : b + b = 10 := by
  rw [h] at *
  exact h2

example (a b : Nat) (h : a = b) : b = a := by
  rw [h]

example (a b : Nat) (h : a = b) : b = a := by
  rw [← h]

example (a b : Nat) (h : a = b) : a + a = b + b := by
  rw [h]

-- example (a : Nat) : a + a = a + a := by
--   nth_rewrite 1 [← Nat.add_zero a]  -- Only rewrite first 'a'
--   rw [Nat.add_zero]

example (n : Nat) : n + 0 = n := by
  rw [Nat.add_zero]

example (n : Nat) : n + 0 = n := by simp

example (a b : Nat) : a + 0 + b + 0 = b + a := by
  simp [Nat.add_comm]

example (a b : Nat) : a + 0 + b + 0 = b + a := by
  rw [Nat.add_zero, Nat.add_zero, Nat.add_comm]

theorem list_append_assoc (xs ys zs : List α):
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil =>
    rw [List.nil_append, List.nil_append]
  | cons h t ih =>
    rw [List.cons_append, List.cons_append, List.cons_append]
    rw [ih]

-- example (n : Nat) : n + 0 + 0 = n := by
--   rw [Nat.add_zero, Nat.add_zero]

example (a b : Nat) (h1 : a = b) (h2 : a + 5 = 10) : b + 5 = 10 := by
  rw [h1] at h2
  exact h2

example (a b : Nat) (h : a + 1 = b) : b = a + 1 := by
  rw [← h]
