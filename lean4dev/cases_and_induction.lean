example (b : Bool) : b = true ∨ b = false := by
  cases b with
  | true =>
    left
    rfl
  | false =>
    right
    rfl

example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero =>
    left
    rfl
  | succ m =>
    right
    omega

example (P Q R : Prop) (h : P ∨ Q) (hpq : P → R) (hqr : Q → R) : R := by
  cases h with
  | inl hp => exact hpq hp
  | inr hq => exact hqr hq


example (P Q : Prop) (h : P ∧ Q) : Q := by
  cases h with
  | intro left right => exact right

theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp [ih]

-- theorem length_append (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length := by
--   induction xs with
--   | nil => simp
--   | cons h t ih => simp [ih]

-- theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
--   induction c with
--   | zero => simp
--   | succ n ih => simp [Nat.add_succ, ih]

example (n : Nat) : n = 0 ∨ n > 0 := by
  match n with
  | 0 =>
    left
    rfl
  | n + 1 =>
    right
    omega

example (b : Bool) : ¬¬b = b := by
  cases b with
  | true => simp
  | false => simp

theorem reverse_reverse (xs : List α) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => simp
  | cons h t ih => simp [ih]

example (o : Option Nat) : o = none ∨ ∃ n, o = some n := by
  cases o with
  | none =>
    left
    rfl
  | some val =>
    right
    exact ⟨val, rfl⟩

theorem append_nil (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

-- example (b : Bool) : b && true = b := by
--   cases b with
--   | true => rfl
--   | false => rfl

example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp [ih]
