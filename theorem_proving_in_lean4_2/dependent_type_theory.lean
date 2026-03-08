def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

#check m
#check n
#check n + 0

#check Nat
#check Bool
#check Nat → Bool

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check β
#check F
#check G

#check Prod α β
#check α × β

#check Prod Nat Nat

#check List α

#check List Nat

#check Type
#check Type 1
#check Type 2
#check Type 3
-- same as Type
#check Type 0

#check List
#check Prod

universe u
def F2 (α : Type u) : Type u := Prod α α

#check F2

def F3.{v} (α : Type v) : Type v := Prod α α

#check F3

#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5

def double (x : Nat) : Nat := x + x

#eval double 3
