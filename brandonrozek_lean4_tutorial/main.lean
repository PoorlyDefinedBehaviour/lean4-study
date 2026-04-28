-- https://brandonrozek.com/blog/lean4-tutorial/

example {p q : Prop} (H_p : p) (H_q : q) : (p ∧ q) := by
  exact show p ∧ q from And.intro H_p H_q

#eval 2 + 2

example {p q : Prop} (H_p : p) (H_q : q) : (p ∧ q) := by
  constructor
  case left => exact show p from H_p
  case right => exact show q from H_q

example {p q : Prop} (H_pq : p ∧ q) : p := by
  exact show p from And.left H_pq

example {p q : Prop} (H_p : p) : (p ∨ q) := by
  exact show p ∨ q from Or.intro_left q H_p

example {p q : Prop} (H_p : p) : (p ∨ q) := by
  left
  exact show p from H_p

example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := by
  exact show r from Or.elim H_pq H_pr H_qr

example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := by
  cases H_pq
  case inl h => exact H_pr h
  case inr h => exact H_qr h

axiom LEM {p : Prop} : p ∨ ¬p

example {α : Type} {P : α → Prop} (y : α) (H : ∀ x : α, P x) : P y := by
  exact show P y from H y

example {α : Type} {P Q R : α → Prop} (H_pq : ∀ x : α, P x → Q x) (H_qr : ∀ x : α, Q x → R x) :
  ∀ x : α , P x → R x := by
  intro (y : α)
  have p1 := H_pq y
  have p2 := H_qr y
  intro (H_py : P y)
  exact p2 (p1 H_py)

example {α : Type} {P : α → Prop} {y : α} (H : P y) : ∃ x : α, P x := by
  exact Exists.intro y H

example {α : Type} {P : α → Prop} {y : α} (H : P y) : ∃ x : α, P x := by
  exact by exists y

example {α : Type} {p : α → Prop} {b : Prop} (H_epx : ∃ x, p x) (H_pab : ∀ (a : α), p a → b) : b := by
  cases H_epx
  case intro a pa => exact H_pab a pa

example {α : Type} {p : α → Prop} {b : Prop} (H_epx : ∃ x, p x) (H_pab : ∀ (a : α), p a → b) : b := by
  match H_epx with
  | .intro a pa => exact H_pab a pa

example {α : Type} {p : α → Prop} {b : Prop} (H_epx : ∃ x, p x) (H_pab : ∀ (a : α), p a → b) : b := by
  exact Exists.elim H_epx H_pab

inductive CustomList (T: Type) where
| cnil : CustomList T
| ccons (hd : T) (tl : CustomList T) : CustomList T

open CustomList

def clength {α : Type} : CustomList α → Nat
| cnil => 0
| ccons _ tl => 1 + clength tl

#eval clength (@cnil Nat)
#eval clength (ccons 2 (ccons 1 cnil))

def cappend {α : Type} (as bs : CustomList α) : CustomList α :=
  match as with
  | cnil => bs
  | ccons a as => ccons a (cappend as bs)

#eval cappend (ccons 1 cnil) (ccons 2 cnil)

theorem append_nil {α : Type} (as : CustomList α) : cappend as cnil = as := by
  have H_BASE : cappend cnil cnil = @cnil α := by rfl

  have H_Inductive : ∀ (hd : α) (tl : CustomList α), cappend tl cnil = tl → cappend (ccons hd tl) cnil = ccons hd tl := by
    intro (hd : α)
    intro (tl : CustomList α)
    intro (IH : cappend tl cnil = tl)
    calc
      cappend (ccons hd tl) cnil = ccons hd (cappend tl cnil) := by rw [cappend]
      _ = ccons hd tl := by rw [IH]

  exact CustomList.recOn (motive := λx ↦ cappend x cnil = x)
    as
    H_BASE
    H_Inductive

theorem append_nil2 {α : Type} (as : CustomList α) : cappend as cnil = as := by
  induction as
  case cnil =>
    rw [cappend]
  case ccons hd tl ih =>
    rw [cappend]
    rw [ih]
