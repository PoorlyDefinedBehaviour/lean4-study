
theorem double_sum (n : Nat) : 2 * n = n + n := by
  induction n with
  | zero => rfl
  | succ n ih => omega

theorem intro_example (P Q : Prop) : P → Q → P := by
  intro hp -- assume p, calling it hp
  intro _ -- assumes Q (unused)
  exact hp -- goal is now P, which we have as hp

theorem forall_intro (P : Nat → Prop) (h : ∀ n , P n) : ∀ m, P m := by
  intro m -- introduces arbitrary m
  exact h m -- apply universal hypothesis

theorem cases_example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R): R := by
  cases h with
  | inl p => exact hp p
  | inr q => exact hq q

theorem and_elim (P Q : Prop) (h : P ∧ Q): P := h.1

theorem exists_elim (P : Nat → Prop) (h : ∃ n, P n ∧ n > 0) : ∃ m, P m := by
  obtain ⟨n, hn, _⟩ := h
  exact ⟨n, hn⟩

theorem rewrite_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  rw [h2]
  -- or simp [h1,h2]
  -- or rw [h1,h2]

theorem rewrite_reverse (a b : Nat) (h : a = b) : b = a := by
  rw [← h]
  -- or rw [h]

theorem simp_example (xs : List Nat) : (xs ++ []).length = xs.length := by
  simp

theorem direct (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp

theorem by_cases_template (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n with
  | zero =>
    left
    rfl
  | succ m =>
    right
    simp

theorem by_induction (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp [ih]

-- ???
-- theorem by_contradiction (P : Prop) (h : ¬¬P) : P := by
--   by_contra hnp
--   exact h hnp

-- ???
-- theorem by_contraposition (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
--   intro hp
--   by_contra hnq
--   exact h hnq hp

theorem backward_example (P Q R : Prop) (hpq : P → Q) (hqr: Q → R) (hp : P) : R := by
  apply hqr
  apply hpq
  exact hp

theorem have_example (a b : Nat) (ha : a > 5) (hb : b < 10) : a + b > 5 := by
  have h1 : a ≥ 6 := ha
  have h2 : b ≥ 0 := Nat.zero_le b
  omega

-- ???
-- theorem calc_example (a b c : Nat) (h1 : a = b + 1) (h2 : b = c + 1) : a = c + 2 := by
--   calc a = b + 1 := h1
--        _ = (c + 1) + 1 := by rw [h2]
--        _ = c + 2 := by ring

theorem obtain_example (h : ∃ n : Nat, n > 0 ∧ n < 10) : ∃ m, m < 10 := by
  obtain ⟨n, _, hlt⟩ := h
  exact ⟨n, hlt⟩

theorem nat_induction (P : Nat → Prop) (base : P 0) (step : ∀ n, P n → P (n + 1))
  : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact step n ih

theorem strong_inductio (n : Nat) (h : n > 0) : n ≥ 1 := by omega

theorem list_induction (xs : List Nat) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

def abs (n : Int) : Int := if n < 0 then -n else n

-- Missing mathlib
-- theorem abs_nonneg (n : Int) : abs n ≥ 0 := by
--   unfold abs
--   split_ifs with h
--   · omega
--   · omega

theorem by_cases_example (P : Prop) [Decidable P] : P ∨ ¬P := by
  by_cases h : P
  · left
    exact h
  · right
    exact h

theorem small_cases (n : Nat) (h : n < 3) : n = 0 ∨ n = 1 ∨ n = 2 := by omega

theorem contradiction_example (P : Prop) (h : P) (hn : ¬P) : False := by
-- ¬P is P → False
-- So give P and get False
  have x := hn h
  exact x

theorem omega_example (a b : Nat) (h : a + b = 10) (h2 : a ≤ 3) : b ≥ 7 := by
  omega

-- theorem ring_example (x y : Int) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring

theorem simp_list (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by simp

-- theorem aesop_example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by aesop
