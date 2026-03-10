universe u v w

def polyIdentity (α : Sort u) (a : α) : α := a

def maxLevel (α : Type u) (β : Type v) : Type (max u v) := α × β

example : Type 0 = Sort 1 := rfl
example : Prop = Sort 0 := rfl

def propPredicate (P : Type U → Prop) : Prop := ∀ α, P α

def typePredicate (P : Type u → Type v) : Type (max (u + 1) v) := ∀ α, P α

#check (Nat : Type 0)
#check (Type 0 : Type 1)
#check (Type 1 : Type 2)

def myId.{uu} (α : Type uu) (x : α) : α := x

#check myId Nat 42
#check myId (Type 0) Nat

def predicativeExample : Type 1 := ∀ (α: Type 0), α → α

#check (∀ (α : Type 0), α → α : Type 1)
#check (∀ (α : Type 1), α → α : Type 2)

def impredicativeExample : Prop := ∀ (P : Prop), P → P

#check (∀ (P : Prop), P → P  : Prop)

def excludedMiddleType : Prop := ∀ (P : Prop), P ∨ ¬P

#check (Nat : Type 0)

def wantsType1 (α : Type 1) : Type 1 := α

#check wantsType1 Nat

#check wantsType1 (ULift Nat)

def Container (α : Type 1) := List α

#check Container Nat

def sumLifted (xs : List (ULift Nat)) : Nat :=
  xs.foldl (λacc x ↦ acc + x.down) 0

def liftedFalse : Type := PLift False
def liftedNat : Type u := ULift.{u} Nat

def liftExample : ULift.{1} Nat := ⟨42⟩

example : liftExample.down = 42 := rfl

def needsLifting (α : Type 1) : Type 2 := ULift.{2} α

theorem and_intro (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

theorem or_elim (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R :=
  h.elim hp hq

theorem iff_intro (P Q : Prop) (hpq : P → Q) (hqp : Q → P) : P ↔ Q :=
  ⟨hpq, hqp⟩

theorem proof_irrel_demo (P : Prop) (p1 p2 : P) : p1 = p2 := rfl

open Classical in
theorem excluded_middle (P : Prop) : P ∨ ¬P := Classical.em P

theorem constructive_exists : ∃ n : Nat, n * n = 4 :=
  ⟨2, rfl⟩

def constructive_even : {n : Nat // n % 2 = 0} :=
  ⟨4, rfl⟩

#eval constructive_even
#eval constructive_even.val

theorem lem (P : Prop) : P ∨ ¬P := Classical.em P

theorem dne (P : Prop) : ¬¬P → P := Classical.byContradiction

theorem even_not_odd (n : Nat) : n % 2 = 0 → ¬(n % 2 = 1) := by
  intro even odd
  omega

noncomputable def classical_witness (P : Nat → Prop) (h : ∃ n, P n) : Nat :=
  Classical.choose h

theorem classical_witness_spec (P : Nat → Prop) (h : ∃ n, P n) : P (classical_witness P h) :=
  Classical.choose_spec h

def decidable_witness (p : Nat → Bool) (bound : Nat) : Nat :=
  (List.range bound).find? (λn ↦ p n) |>.getD 0

def boolToNat : Bool → Nat
  | true => 1
  | false => 0

def natToBool : Nat → Bool
  | 0 => false
  | _ => true

def sumUnitEquivBool : Unit ⊕ Unit ≃ Bool where
  toFun
    | .inl () => false
    | .inr () => true
  invFun
    | false => .inl ()
    | true => .inr ()
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl
