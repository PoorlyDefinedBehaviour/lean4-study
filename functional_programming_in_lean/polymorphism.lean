structure PPoint (α : Type) where
  x : α
  y : α

#check (PPoint)

def natOrigin : PPoint Nat :=
  {x := Nat.zero, y := Nat.zero}

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check (replaceX)

#check replaceX Nat

#eval replaceX Nat natOrigin 5

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) :
  match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

def primesUnder10 : List Nat := [2, 3, 5, 7]

-- inductive List (α : Type) where
--   | nil : List α
--   | cons : α → List α → List α

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length α ys)

#eval length String ["Sourdough", "bread"]

def length2 (α : Type) (xs : List α ) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length2 α ys)

def replaceX2 {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

def length3 {α : Type} (xs : List α ) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length3 ys)

#check List.length (α := Int)

-- inductive Option (α : Type) : Type where
--   | none : Option α
--   | some (val : α) : Option α

-- def List.head? {α : Type} (xs : List α) : Option α :=
--   match xs with
--   | [] => none
--   | x :: _ => some x

#eval primesUnder10.head?

#eval [].head? (α := Int)
#eval ([] : List Int).head?

-- structure Prod (α : Type) (β : Type) : Type where
--   fst : α
--   snd : β

-- Same thing
def fives : String × Int := {fst := "five", snd := 5}
def fives2 : String × Int := ("five", 5)

-- inductive Sum (α : Type) (β : Type) : Type where
--   | inl : α →  Sum α β
--   | inr : β → Sum α β

def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals

-- inductive Unit : Type where
--   | unit : Unit

inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann →  ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann →  ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann →  ArithExpr ann → ArithExpr ann

#eval () : Unit
