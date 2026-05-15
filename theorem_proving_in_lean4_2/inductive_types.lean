inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
deriving Repr

inductive Weekday2 where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday

open Weekday

def numberOfDay : Weekday → Nat
  | sunday => 1
  | monday => 2
  | tuesday => 3
  | wednesday => 4
  | thursday => 5
  | friday => 6
  | saturday => 7

#eval tuesday

namespace Weekday
def next : Weekday → Weekday
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous : Weekday → Weekday
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

example : next (previous tuesday) = tuesday := rfl

theorem foo : ∀d : Weekday, next (previous d) = d := by
  intro d
  match d with
  | sunday    =>
    simp [previous, next]
  | monday    =>
    simp [previous, next]
  | tuesday   =>
    simp [previous, next]
  | wednesday =>
    simp [previous, next]
  | thursday  =>
    simp [previous, next]
  | friday    =>
    simp [previous, next]
  | saturday  =>
    simp [previous, next]

theorem foo2 : ∀d : Weekday, next (previous d) = d := by
  intro d
  cases d <;> rfl

theorem foo3 (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

theorem foo4 (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

end Weekday

inductive Bool2 where
| false : Bool2
| true : Bool2

def and (a b : Bool2) : Bool2 :=
  match a with
  | .true => b
  | .false => .false

def or (a b : Bool2) : Bool2 :=
  match a with
  | .true => .true
  | .false => b

inductive Prod2 (α : Type u) (β : Type v)
| mk : α → β → Prod2 α β

inductive Sum2 (α : Type u) (β : Type v) where
| inl : α → Sum2 α β
| inr : β → Sum2 α β

def fst : Prod α b → α
| .mk a _ => a

def snd : Prod α β → β
| .mk _ b => b

def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := λ_ ↦ Nat) p
    (λ b n ↦ cond b (2 * n) (2 * n + 1))

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := λ_ ↦ Nat) s
    (λn ↦ 2 * n)
    (λn ↦ 2 * n + 1)

structure Prod3 (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β

structure Color where
  red : Nat
  green : Nat
  blue : Nat
deriving Repr

def yellow := Color.mk 255 255 0

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc: ∀ a b c, mul (mul a b) c = mul a (mul b c)

inductive Option2 (α : Type u) where
| none : Option2 α
| some : α → Option2 α

inductive Inhabited2 (α : Type u) where
| mk : α → Inhabited2 α

inductive False2 : Prop

inductive True2 : Prop where
| intro : True2

inductive And2 (a b : Prop) : Prop where
| intro : a → b → And2 a b

inductive Or2 (a b : Prop) : Prop where
| inl : a → Or2 a b
| inr : b → Or2 a b

inductive Exists2 {α : Sort u} (p : α → Prop) : Prop where
| intro (w : α) (h : p w) : Exists2 p

inductive Subtype2 {α : Type u} (p : α → Prop) where
| mk : (x : α) → p x → Subtype2 p

inductive Nat2 where
| zero : Nat2
| succ : Nat2 → Nat2
deriving Repr

def add (m n : Nat2) : Nat2 :=
  match n with
  | .zero => m
  | .succ n => .succ (add m n)

instance : Add Nat2 where
  add := add

theorem add_zero (m : Nat2) : m + Nat2.zero = m := rfl
theorem add_succ (m n : Nat2) : m + Nat2.succ n = Nat2.succ (m + n) := rfl

namespace List2
inductive List (α : Type u) where
| nil : List α
| cons (h : α) (t : List α) : List α

def append (as bs : List α) : List α :=
  match as with
  | .nil => bs
  | .cons a as => .cons a (append as bs)

theorem nil_append (as : List α) : append .nil as = as := rfl

theorem cons_append (a : α) (as bs : List α) : append (.cons a as) bs = .cons a (append as bs) := rfl

theorem append_nil (as : List α) : append as .nil = as :=
  match as with
  | .nil => rfl
  | .cons a as =>
    by
      simp [append, append_nil as]

theorem append_nil2 (as : List α) : append as .nil = as := by
  induction as with
  | nil =>
    unfold append
    rfl
  | cons a as ih =>
    simp [append, ih]

end List2
