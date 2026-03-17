import Std.Data.HashMap

def LengthList (α : Type u) : Nat → Type u
  | 0 => PUnit
  | Nat.succ n => α × LengthList α n

example : LengthList Int 0 := ()

example : LengthList String 2 := ("Hello", "there", ())

-- example : LengthList String 5 := ("Wrong", "number", ())

def two : (b : Bool) →  if b then Unit × Unit else String :=
  λb ↦
    match b with
    | true => ((), ())
    | false => "two"

example : ((x : Nat) → String) = (Nat → String) := rfl

example : ((n : Nat) → n + 1 = 1 + n) = ((k : Nat) → k + 1 = 1 + k) := rfl

def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (lt : i < xs.size) → xs[i] ≠ 0

-- Doesn't compile
-- def AllNonZeroNonDependent (xs : Array Nat) : Prop :=
--   (i : Nat) → (i < xs.size) → xs[i] ≠ 0

example :
  ({α : Type} → (x : α) → α)
  =
  ((α : Type) → (x : α) → α)
  := rfl

def thirdChar (xs : Array Char) : Char := xs[2]!

example : thirdChar #['!'] = thirdChar #['-', 'x'] := rfl

example : thirdChar #['!'] = 'A' := rfl
example : thirdChar #['-', 'x'] = 'A' := rfl

#eval (List.reverse ∘ List.drop 2) [3, 2, 4, 1]
#eval Function.comp List.reverse (List.drop 2) [3, 2, 4, 1]

#eval Function.const Bool 10 true
#eval Function.const Bool 10 false

#eval Function.curry Prod.swap 3 "five" = ("five", 3)

#eval Function.uncurry List.drop (1, ["a", "b", "c'"])

example : Sort 5 := Sort 4
example : Sort 2 := Sort 1

example : Sort 1 := Unit
-- example : Sort 2 := Unit

example : Prop := ∀ (P : Prop) (p1 p2 : P), p1 = p2

example : Prop := ∀ (α : Type), ∀ (x : α), x = x
example : Prop := ∀ (α : Type 5), ∀ (x : α), x = x

example (α : Type 1) (β : Type 2) : Type 2 := α → β
example (α : Type 2) (β : Type 1) : Type 2 := α → β

-- Compile error
-- example (α : Type 2) (β : Type 1) : Type 1 := α → β

-- Compile error
-- example (α : Type 2) (β : Type 1) : Type 3 := α → β

structure Codec.{u} : Type (u + 1) where
  type : Type u
  encode : Array UInt32 → type → Array UInt32
  decode : Array UInt32 → Nat → Option (type × Nat)

def Codec.char : Codec where
  type := Char
  encode buf ch := buf.push ch.val
  decode buf i := do
    let v ← buf[i]?
    if h : v.isValidChar then
      let ch : Char := ⟨v, h⟩
      return (ch, i + 1)
    else
      failure

inductive Vacant : Type where

inductive No : Prop where

inductive Solo where
  | solo

#check Solo
#check Solo.solo

inductive Yes : Prop where
  | intro

#check Yes
#check Yes.intro

inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (¬isEven)

example : EvenOddList String true := .cons "a" (.cons "b" .nil)

-- Compile error
-- example : EvenOddList String true := .cons "a" (.cons "b" (.cons "c" .nil))

inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | left : α → Either α β
  | right : β → Either α β

inductive AtLeastOne (α : Type u) : Type u where
  | mk : α → Option (AtLeastOne α) → AtLeastOne α

def oneTwoThree : AtLeastOne Nat := ⟨1, some ⟨2, some ⟨3, none⟩⟩⟩

def AtLeastOne.head : AtLeastOne α → α
  | ⟨x, _⟩ => x

def oneTwoThree' : AtLeastOne Nat :=
  .mk 1 (some (.mk 2 (some (.mk 3 none))))

def AtLeastOne.head' : AtLeastOne α → α
  | .mk x _ => x

structure MyProd (α β : Type _) where
  fst : α
  snd : β

structure Graph where
  adjacency : Array (List Nat) := #[]

def Graph.empty : Graph := {}
#eval Graph.empty.1

structure Palindrome where
  ofString ::
  text : String
  is_palindrome : text.data.reverse = text.data

#check (Palindrome.ofString "aba" (by decide))
-- #check (Palindrome.ofString "ab" (by decide))


structure NatStringBimap where
  private mk::
  natToString : Std.HashMap Nat String
  stringToNat : Std.HashMap String Nat

def NatStringBimap.empty : NatStringBimap := ⟨{}, {}⟩

def NatStringBimap.insert (nat : Nat) (string : String) (map : NatStringBimap) : Option NatStringBimap :=
  if map.natToString.contains nat ∨ map.stringToNat.contains string then
    none
  else
    some <|
      NatStringBimap.mk
        (map.natToString.insert nat string)
        (map.stringToNat.insert string nat)

structure AugmentedIntList where
  list : List Int
  augmentation : String := ""

def AugmentedIntList.isEmpty : AugmentedIntList → Bool
  | {list := []} => true
  | _ => false

#eval {list := [], augmentation := "extra" : AugmentedIntList}.isEmpty

def location : Float × Float where
  fst := 22.807
  snd := -13.923
