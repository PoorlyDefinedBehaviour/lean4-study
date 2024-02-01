def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat -- Nat → List Nat → List Nat
#check cons Bool -- Bool → List Bool → List Bool
#check cons -- (α : Type) (a : α) (as : List α) : List α

#check @List.cons -- {α : Type u_1} → α → List α → List α
