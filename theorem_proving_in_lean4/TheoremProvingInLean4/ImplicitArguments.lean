def as : List Nat := List.nil

def bs : List Nat := List.cons 5 (List.nil)

universe u

def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α :=
  List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) := List.append as bs

def as2 : Lst Nat := Lst.nil
def bs2 : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs -- List Nat

def ident {α : Type u} (x : α) := x

#check ident -- ident.{u} {α : Type u} (x : α) : α
#check ident 1 -- Nat

#check @id -- @id: {α : Sort u_1} → α → α
#check @id Nat -- Nat → Nat
