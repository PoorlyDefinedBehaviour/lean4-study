example : True → True := by
  intro h
  -- trivial
  -- or
  -- exact True.intro
  -- or
  exact h

example (P : Prop) : P → P := by
  intro hp
  exact hp

example : ∀ n : Nat, n = n := by
  intro n
  rfl

example : ∀ a b : Nat, a + b = b + a := by
  intro a b
  exact Nat.add_comm a b

-- example : ∀ a b c : Nat, a + b + c = c + b + a := by
--   intro a b c
--   ring

example : ∀ (P Q : Prop), P → Q → P := by
  intro P Q hp hq
  exact hp

example : ∀ (n : Nat), n > 0 → n ≥ 1 := by
  intro n
  intro h
  omega

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

example : (∃ n : Nat, n > 5) → ∃ n : Nat, n > 0 := by
  intro ⟨n, hn⟩
  exact ⟨n, by omega⟩

-- example : ∀ a b : Nat, a = b → b = a := by
--   intros
--   -- Introduces a, b, and the equality proof with auto-generated names
--   assumption

example : ∀ a b : Nat, a = b → b = a := by
  intro a b hab
  exact hab.symm

example (P Q : Prop) : P → Q → Q := by
  intro hp hq
  exact hq

example : ∀ n : Nat, n + 0 = n := by
  intro n
  simp

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

-- These are equivalent
example : Nat → Nat := λn ↦ n + 1
example : Nat → Nat := by intro n; exact n + 11

example (P Q : Prop) (f : P → Q) (hp : P) : Q := by
  apply f
  exact hp

example (P Q : Prop) (f : P → Q) (hp : P) : Q := f hp

theorem t1 : ∀ n : Nat, n = n := by intro n; rfl
theorem t2 : ∀ n : Nat, n = n := λn ↦ rfl
#print t1
#print t2

example (P Q R : Prop) : (P → Q)
→ (Q → R) → P → R := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

example : ∀ n : Nat, n > 0 → n ≠ 0 := by
  intro n hn
  omega

example : ∀ (f : Nat → Nat), (∀ n, f n = n) → f 5 = 5 := by
  intro f hf
  exact hf 5
