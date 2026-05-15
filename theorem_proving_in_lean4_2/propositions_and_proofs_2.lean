#check And
#check Or
#check Not
-- #check Implies

-- #check Proof

variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := λp ↦ λ_ ↦ p
theorem t2 : p → q → p := λp _ ↦ p

#print t1
#print t2

theorem t3 : p → q → p :=
  λhp ↦
  λ_ ↦
  show p from hp

#print t3


example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q): q := And.right h

variable (xs : List Nat)
#check List.length xs
#check xs.length

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

example (hp : p) : p ∨ q := Or.intro_left q hp
example (hp : q) : p ∨ q := Or.intro_right p hp

variable (r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
  (λhp ↦ Or.inr hp)
  (λhq ↦ Or.inl hq)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h Or.inr Or.inl

example (hpq : p → q) (hnq: ¬q) : ¬p :=
  λp ↦ hnq (hpq p)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
  (λ⟨p, q⟩ ↦ ⟨q, p⟩)
  (λ⟨q, p⟩ ↦ ⟨p, q⟩)

variable (h : p ∧ q)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

open Classical

#check em p

theorem dne (h : ¬¬p) : p :=
  Or.elim (em p)
  (λp ↦ p)
  (λnotp ↦ absurd notp h)
