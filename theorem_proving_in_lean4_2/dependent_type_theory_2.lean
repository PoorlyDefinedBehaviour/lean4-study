def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

#check true

#check Nat → Nat

#check Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check G α Nat

#check List α

#check Type

#check Type
#check Type 0
#check List

universe u

def FF (α : Type u) : Type u := Prod α α
#check FF

def FFF.{v} (α : Type v) : Type v := Prod α α
#check FFF

#check λ(x: Nat) ↦ x + 5

def double (x : Nat) : Nat := x + x

theorem double_eq_times_2 (x : Nat) : double x = 2 * x := by
  unfold double
  omega

def double2 := λ(x: Nat) ↦ x + x

theorem double_eq_double2 (x : Nat) : double x = double2 x := by
  unfold double double2
  rfl

def greater (x y : Nat) :=
  if x > y then x else y

def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

def twice_double (x : Nat) : Nat :=
  let y := x + x
  y * y

variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

def doTwice (h : α → α) (x : α) : α := h (h x)

def doThrice (h : α → α) (x : α) : α := h (h (h x))

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)
  def compose2 := g (f x)
  def doTwice2 := h (h x)
  def doThrice2 := h (h (h x))
end useful

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a

def cons (α : Type) (a : α) (as : List α) : List α := List.cons a as

#check cons Nat

#check @List.cons
