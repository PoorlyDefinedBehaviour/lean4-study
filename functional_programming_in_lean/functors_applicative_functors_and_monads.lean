structure MythicalCreature where
  large : Bool
deriving Repr

#check MythicalCreature.mk

#check MythicalCreature.large

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr

def troll : Monster where
  large := true
  vulnerability := "sunlight"

#check Monster.mk

#check Monster.toMythicalCreature

#eval troll.toMythicalCreature

#check troll.toMythicalCreature

def troll2 : Monster := ⟨⟨true⟩, "sunlight"⟩

#eval MythicalCreature.large troll

def MythicalCreature.small (c : MythicalCreature) : Bool := ¬c.large

#eval troll.small
#eval MythicalCreature.small troll

structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

def nisse : Helper where
  large := false
  assistance := "household tassks"
  payment := "porridge"

structure MonstrousAssistant extends Monster, Helper where
deriving Repr


def domesticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"

#check MonstrousAssistant.mk

#print MonstrousAssistant.toHelper

inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large

def nonsenseCreature : SizedCreature where
  large := false
  size := .large

abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)

def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by decide

instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()

instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()

structure Pair (α β : Type) : Type where
  first : α
  second : β

instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩

structure RawInput where
  name : String
  birthYear : String

-- structure Subtype {α : Type} (p : α → Prop) where
--   val : α
--   property : p val

def FastPos : Type := {x : Nat // x > 0}

def one : FastPos := ⟨1, by decide⟩

instance : OfNat FastPos (Nat.succ n) where
  ofNat := ⟨Nat.succ n, by simp⟩

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else
    none

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance : Coe (NonEmptyList α) (List α) where
  coe
    | {head := x, tail := xs} => x :: xs

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }

structure CheckedInput (thisYear : Nat) : Type where
  name : { n : String // n ≠ "" }
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α

instance : Functor (Validate ε) where
  map f
    | .ok => .ok (f x)
    | .errors errs => .errors errs

instance : Append (NonEmptyList α) where
  append l1 l2 := {head := l1.head, tail := l1.tail ++ [l2.head] ++ l2.tail}


instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Field := String
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors {head := (f, msg), tail := []}

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else
    pure (name, h)

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear (thisYear year : Nat) : Validate (Field × String) {y : Nat // y > 1900 ∧ ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure (year, by simp [*])
    else
      reportError "birth year" s!"Must be no later than {thisYear}"
  else
    reportError "birth year" "Must be after 1900"

def checkInput (year : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
  checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearASNat =>
      checkBirthYear year birthYearASNat

#check Type
#check Type → Type
#check Type 1

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def myListOfNat : MyList Type := .cons Nat .nil

inductive MyList2 (α : Type u) : Type u where
  | nil : MyList2 α
  | cons : α → MyList2 α → MyList2 α

def myListOfNumbers : MyList2 Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat2 : MyList2 Type :=
  .cons Nat .nil

def myListOfSelf : MyList2 (Type → Type) :=
  .cons MyList2 .nil

-- inductive Sum (α : Type u) (β : Type v) : Type (max u v) where
--   | inl : α → Sum α β
--   | inr: β → Sum α β

def stringOrType : Sum String Type := .inr Nat
