example : 2 + 2 = 4 := rfl

example : 2 + 2 = 4 := by
  rfl

example : True ∧ True := by
  constructor
  · trivial
  · trivial

example : True ∧ True := by
  constructor <;> trivial

example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]

theorem symmetry (a b : Nat) (h : a = b) : b = a := by
  rw [h]

theorem myThm : 2 + 2 = 4 := by rfl

#print myThm

example (a b : Nat) : a + b = b + a := by
  simp [Nat.add_comm]
