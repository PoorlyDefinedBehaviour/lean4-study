def identity {α : Type} (x : α) : α := x

#eval identity 42

def compose {α β γ : Type} (g : β → γ) (f : α → β) : α → γ :=
  fun x => g (f x)

-- def flip {α β γ} (f : α → β γ) : β → α → γ :=
--   λb a ↦ f a b

def Pair (α β : Type) := α × β

def makePair {α β : Type} (a : α) (b : β) : Pair α β := (a, b)

inductive Either (α β : Type) where
  | left : α → Either α β
  | right : α → Either α β
deriving Repr

def mapEither {α β γ} (f : β → γ) : Either α β → Either α γ
  | .left a => .left a
  | .right b => .right (f b)

def listLength {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: rest => 1 + listLength rest

def firstOrDefault {α : Type} (xs : List α) (default : α) : α :=
  match xs with
  | [] => default
  | x :: _ => x

def printTwice {α : Type} [ToString α] (x : α) : String :=
  s!"{x} and {x}"

def maximum {α : Type} [Ord α] (xs : List α) : Option α :=
  xs.foldl (init := none) λacc x ↦
    match acc with
    | none => some x
    | some m => if compare x m == .gt then some x else some m

class Printable (α : Type) where
  format : α → String

instance : Printable Nat where
  format n := s!"Nat({n})"

instance : Printable Bool where
  format b := if b then "yes" else "no"


def showValue {α : Type} [Printable α] (x : α) : String :=
  Printable.format x

instance {α : Type} [Printable α] : Printable (List α) where
  format xs :=
    let items := xs.map Printable.format
    "[]" ++ ", ".intercalate items ++ "]"

class Addable (α : Type) where
  add : α → α → α
  zero : α

instance : Addable Nat where
  add := Nat.add
  zero := 0

def sumList {α : Type} [Addable α] (xs : List α) : α :=
  xs.foldl Addable.add Addable.zero

class Eq' (α : Type) where
  eq : α → α → Bool

class Ord' (α : Type) extends Eq' α where
  lt : α → α → Bool

instance : Eq' Nat where
  eq := (· == ·)

instance : Ord' Nat where
  eq := (· == ·)
  lt := (· < ·)

class Functor' (F : Type → Type) where
  map : {α β : Type} → (α → β) → F α → F β

instance : Functor' List where
  map := List.map

instance : Functor' Option where
  map f
    | none => none
    | some x => some (f x)

@[simp] theorem add_zero_right' (n : Nat) : n + 0 = n := Nat.add_zero n

class Semigroup (α : Type) where
  append : α → α → α

class Monoid' (α : Type) extends Semigroup α where
  empty : α

def concat {α : Type} [Monoid' α] (xs : List α) : α :=
  xs.foldl Semigroup.append Monoid'.empty

instance : Monoid' String where
  append := String.append
  empty := ""

instance {α : Type} : Monoid' (List α) where
  append := List.append
  empty := []

#eval concat ["Hello"," ", "world"]
#eval concat [[1, 2], [3], [4, 5]]
