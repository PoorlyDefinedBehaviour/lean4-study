/--
error: Type mismatch
  "Not a number"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in
def x : Nat := "Not a number"

section
variable (x y : Nat)
def double := x + x

#check double x

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1: double (x + y) = double x + double y := by simp [double]
end

namespace Foo
def bar : Nat := 1
end Foo

open Foo in
#check bar

def Foo.baz : Nat := 1

def String.add (a b : String) : String := a ++ b

def Bool.add (a b : Bool) : Bool := a != b

def add (α β : Type) : Type := Sum α β

#check add Nat Nat
#check _root_.add

protected def Foo.bar2 : Nat := 1

/-- error: Unknown identifier `bar2` -/
#guard_msgs in
#check bar2

section
open Nat (succ zero gcd)
#check zero
#eval gcd 15 6
end

section
open Nat hiding succ gcd
#check zero
end

/-- error: Unknown identifier `gcd` -/
#guard_msgs in
#eval gcd 15 6

section
open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3
end

section
export Nat (succ add sub)
end

section
def isPrefix (l1 : List α) (l2 : List α) : Prop :=
  ∃t, l1 ++ t = l2

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as := by
  exact ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by simp

attribute [simp] List.isPrefix_self

instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_self2 (as : List α) : as ≤ as := by
  exact ⟨[], by simp⟩

def instLe : LE (List α) :=
  {le := isPrefix}

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
end

variable (m n : Nat)
variable (i j : Int)

#check i + m
#check i + m + j
#check i + ↑m + j

#check @Eq

#check (· + 1)

#check [1,2,3].foldl

inductive Term where
| var (name : String)
| num (val : Nat)
| app (fn : Term) (arg : Term)
| lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
| Term.lambda (name := n) .. => some n
| _ => none

def getBinderType : Term → Option Term
| Term.lambda (type := t) .. => some t
| _ => none
