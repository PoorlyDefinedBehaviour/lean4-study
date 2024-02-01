#check Nat -- Type
#check Bool -- Type
#check Nat → Bool -- Type

def a : Type := Nat
def b : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check a -- Type
#check F a --Type
#check F Nat -- Type
#check G a -- Type → Type
#check G a b -- Type
#check G a Nat -- Type

#check Prod a b -- Type
#check a × b -- Type
#check Prod Nat Nat -- Type
#check Nat × Nat -- Type

#check List a -- Type
#check List Nat -- Type

#check Type -- Type 1
#check Type 0 -- Type 1
#check Type 1 -- Type 2
#check Type 2 -- Type 3

#check List -- List.{u} (a : Type u) : Type u

universe u

def H (a : Type u) : Type u := Prod a a

#check H -- H.{u} (a : Type u) : Type u
