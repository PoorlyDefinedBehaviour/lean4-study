import Mathlib.Tactic

example (P Q R : Prop) (hP : P) (hPQ: P → Q) (hQR : Q → R) : R := by aesop

example (P Q R : Prop) : (P → Q) → (Q → R) → P → Q := by
  intro hPQ hQR hP
  aesop

example (P Q : Prop) (h : P ∨ Q) (hp : P → Q) : Q := by aesop

example (n : Nat) : n + 0 = n := by aesop

example (h : P ∧ Q): Q := by aesop

def Even (n : Nat) : Prop := Exists λk ↦ n = 2 * k

@[aesop]
lemma even_zero : Even 0 := by
  exact Exists.intro 0 (by simp)

example : Even 0 := by aesop

example (P Q R : Prop) (hP: P) (hPQ: P → Q) (hQR: Q → R) : R := by aesop?
