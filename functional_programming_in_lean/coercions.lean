def fileDumper : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "which file? "
  stdout.flush
  let f := (← stdin.getLine).trimAscii.toString
  stdout.putStrLn s!"'The file {f}' contains:"
  stdout.putStrLn (← IO.FS.readFile f)

-- class Coe (α : Type) (β : Type) where
--   coe : α → β

-- instance : Coe Pos Nat where
--   coe x := x.toNat

-- def oneInt : Int := Pos.one

def List.last2? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: xs => last2? xs

#eval [1,2,3].last2?

def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  ↑(392 : Nat)

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance : Coe (NonEmptyList α) (List α) where
  coe
    | {head := x, tail := xs} => x :: xs

-- class CoeDep (α : Type) (x : α) (β : Type) where
--   coe : β

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Monoid Type where
  coe m := m.Carrier

def foldMap2 (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Bool Prop where
  coe b := b = true

-- class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
--   coe : (x : α) → makeFunctionType x

structure Adder where
  howMuch : Nat

def add5 : Adder := ⟨5⟩

instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)

#eval add5 3

inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
deriving Repr

structure Serializer where
  Contents : Type
  serialize : Contents → JSON

def Str : Serializer :=
  { Contents := String, serialize := JSON.string }

instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]

#eval JSON.null
#eval JSON.string "hello"

#eval (match JSON.string "hello" with | JSON.string x => s!"found {x}" | _ => "oops")

structure Tree : Type where
  latinName : String
  commonNames : List String

def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

def birch : Tree :=
  { latinName := "Betula pendula", commonNames := ["silver birch", "warty birch"] }

def sloe : Tree where
  latinName := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]

class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

instance : Display Tree where
  displayName t := t.latinName

example : NonEmptyList String :=
  {
    head := "Sparrow",
    tail := ["Duck", "Swan"]
  }

example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
