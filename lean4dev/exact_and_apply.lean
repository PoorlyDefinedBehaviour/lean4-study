example (h : 2 + 2 = 4) : 2 + 2 = 4 := by exact h

example : True := by exact trivial

example (a b : Nat) (h : a = b) : a = b := by exact h

example (n : Nat) : n + 0 = n := by exact Nat.add_zero n

example (a b : Nat) : a + b = b + a := by exact Nat.add_comm a b

example : ∀ n : Nat, n = n := by exact λn ↦ rfl

example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  apply Eq.trans
  · exact hab
  · exact hbc

example (h : 1 = 1 → 2 = 2) : 2 = 2 := by
  apply h
  rfl

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp

example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by
  apply congrArg
  exact h

example (P Q : Prop) (hp : P) (hq : Q) : P := by assumption

example (a b : Nat) (h1 : a = b) (h2 : b = a) : b = a := by assumption

example (n : Nat) : n + 0 = n := by exact?

example (a b : Nat) : a + b = b + a := by apply?

example (a b : Nat) : a + b = b + a := by apply Nat.add_comm

example (P Q R : Prop) (f : P → Q) (g : Q → R) (hp : P) : R := by
  apply g
  apply f
  exact hp

example (n : Nat) : 0 + n = n := by exact Nat.zero_add n
