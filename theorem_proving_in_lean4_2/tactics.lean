theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

#print test

theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h1 h2
  exact Eq.trans (Eq.symm h2) h1

example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp =>
    apply Or.inr
    exact hp
  | inr hq =>
    apply Or.inl
    exact hq

def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _ , _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1
