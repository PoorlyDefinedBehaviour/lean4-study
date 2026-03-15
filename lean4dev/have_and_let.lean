example (n : Nat) (h : n > 0) : n * 2 > 0 := by
  have pos : n > 0 := h
  omega

example (a b : Nat) (ha : a > 5) (hb : b > 3) : a + b > 8 := by
  have hab : a + b > 5 + 3 := by omega
  omega

example (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  have hq : Q := by
    apply hpq
    exact hp
  have hr : R := by
    apply hqr
    exact hq
  exact hr

example (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  have hq : Q := hpq hp
  exact hqr hq

example : 10 = 5 + 5 := by
  let x := 5
  -- x : Nat := 5
  rfl

-- example (n : Nat) : n + n = 2 * n := by
--   let m := n + n
--   -- m : Nat := n + n
--   show m = 2 * n
--   ring

example (h : 2 + 2 = 4) : True := by
  have proof : 2 + 2 = 4 := h
  trivial

example : (5 + 5) * 2 = 20 := by
  let ten := 5 + 5
  rfl

example (n : Nat) (h : n > 5) : n > 0 := by
  have : n > 5 := h
  omega

-- example (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
--   have : (a + b) * (a + b) = (a + b)ˆ2 := by ring
--   ring

example (P Q : Prop) (hp : P) (hpq : P → Q) : Q := by
  have hq := hpq hp
  -- hq : Q
  exact hq

example : ∃ n : Nat, n > 10 := by
  let x := 42
  have h := show x > 10 by omega
  exact ⟨x, h⟩

theorem sqrt_two_irrational (p q : Nat) (hq : q ≠ 0) (h : p * p = 2 * q * q) : False := by
  have hp_even : 2 ∣ p := by
    sorry
  have ⟨k, hk⟩ := hp_even
  have hq_even : 2 ∣ q := by
    sorry
  sorry

example (h : ∃ n : Nat, n > 5 ∧ n < 10) : True := by
  have ⟨n, hn_gt, hn_lt⟩ := h
  trivial

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  have ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

example (n : Nat) : n + n ≥ n := by
  suffices h : n ≤ n + n by omega
  omega

example (n : Nat) : n + n ≥ n := by
  have h : n ≤ n + n := by omega
  omega

example (a b : Nat) (h : a = b) : a + a = b + b := by
  have h' : a = b := h
  rw [h']

example : 5 * 5 = 25 := by
  let x := 5
  rfl

example (P Q R : Prop) (hp : P) (f : P → Q) (g : Q → R) : R := by
  have hq : Q := f hp
  have hr : R := g hq
  exact hr

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  have hab : a ≤ b := h1
  have hbc : b ≤ c := h2
  exact Nat.le_trans hab hbc
