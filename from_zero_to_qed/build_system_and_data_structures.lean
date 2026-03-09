import Std.Data.HashMap
import Std.Data.HashSet

def nothing : Unit := ()

def printAndReturn : IO Unit := do
  IO.println "Side effect!"
  return ()

def greetIO (name: String) : IO Unit :=
  IO.println s!"Hello, {name}!"

#eval greetIO "world"

def absurd' {α : Type} (e : Empty) : a :=
  Empty.elim e

def myBool : Bool := true
def myFalse : Bool := false

#eval true ∧ false
#eval true ∨ false
#eval ¬true
#eval true ^^ false -- xor

def absInt (x : Int) : Int :=
  if x < 0 then -x else x

#eval absInt 5
#eval absInt (-5)

#eval if true then "yes" else "no"
#eval if false then "yes" else "no"

def someValue : Option Nat := some 42
def noValue : Option Nat := none

def getOrDefault (opt : Option Nat) (default : Nat) : Nat :=
  match opt with
  | none => default
  | some x => x

#eval getOrDefault (some 10) 0
#eval getOrDefault none 0

def letterA : Char := 'A'
def digit : Char := '7'
def unicode : Char := 'λ'
def bear : Char := '🐻'

#eval 'A'.isAlpha
#eval '7'.isDigit

def greeting : String := "Hello, Lean!"

#eval "Hello".length
#eval "Hello".toList

def shipName := "Mistake Not My Current State Of Alarm"
def shipClass := "GCU"
#eval s!"The {shipClass} {shipName} has entered the system."


#eval "Hello world".take 5
#eval "Hello world".drop 6

#eval "a,b,c".splitOn ","
#eval ",".intercalate ["a", "b", "c"]

def byte : UInt8 := 255
def word : UInt16 := 65535
def dword : UInt32 := 0xDEADBEEF
def qword : UInt64 := 0xCAFEBABE12345678

#eval (255 : UInt8 ) + 1

def platformSize : USize := 42

def signedByte : Int8 := -128
def signedWord : Int16 := -32768

def myFloat : Float := 3.14159

def pair : Nat × String := (42, "answer")
def triple : Nat × String × Bool := (1, "one", true)

#eval pair.1
#eval pair.2
#eval pair.fst
#eval pair.snd

def swap {α β : Type} (p : α × β) : β × α :=
  let (a, b) := p
  (b, a)

#eval swap (1, "hello")


def nested : (Nat × Nat) × String := ((1, 2), "pair")
#eval nested.1
#eval nested.1.1
#eval nested.1.2

def leftValue : Nat ⊕ String := Sum.inl 42
def rightValue : Nat ⊕ String := Sum.inr "hello"

def describeSum (s : Nat ⊕ String) : String :=
  match s with
  | Sum.inl n => s!"A number: {n}"
  | Sum.inr str => s!"A string: {str}"

#eval describeSum leftValue
#eval describeSum rightValue

def divideExcept (x y : Nat) : Except String Nat :=
  if y == 0 then
    Except.error "Division by zero"
  else
    Except.ok (x / y)

#eval divideExcept 10 2
#eval divideExcept 10 0

def myList : List Nat := [1, 2, 3, 4, 5]
def emptyList : List Nat := []

def consExample := 0 :: [1, 2, 3]
def appendExample := [1,2] ++ [3,4]

#eval [1,2,3].length
#eval [1,2,3].head?
#eval [1,2,3].tail?
#eval [1,2,3][1]?
#eval [1,2,3].reverse

#eval [1,2,3].map (· * 2)
#eval [1,2,3,4,5].filter (· > 2)
#eval [1,2,3,4].foldl (· + ·) 0

#eval [1,2].flatMap (λx ↦ [10,20].map (λy ↦ x + y))

def myArray : Array Nat := #[1,2,3,4,5]
def emptyArray : Array Nat := #[]

#eval #[1,2,3].size
#eval #[1,2,3][0]!
#eval #[1,2,3][1]?
#eval #[1,2,3][10]?

#eval #[1,2,3].toList
#eval [1,2,3].toArray

#eval #[1,2,3].map (· * 2)
#eval #[1,2,3,4].filter (· % 2 == 0)

def bytes : ByteArray := ByteArray.mk  #[0x48, 0x65, 0x6C, 0x6C, 0x6F]

#eval bytes.size
#eval bytes.get! 0
#eval bytes.toList

#eval "Hello".toUTF8

def bits8 : BitVec 8 := 0xFF
def bits16 : BitVec 16 := 0xABCD
def bites32 : BitVec 32 := 0xDEADBEEF

open Std in
def myMap : Std.HashMap String Nat :=
  HashMap.emptyWithCapacity
    |>.insert "one" 1
    |>.insert "two" 2
    |>.insert "three" 3

open Std in
def mySet : HashSet Nat :=
  HashSet.emptyWithCapacity
    |>.insert 1
    |>.insert 2
    |>.insert 3
    |>.insert 2  -- duplicate ignored

#eval myMap
#eval mySet

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := ⟨0.0, 0.0⟩
def myPoint : Point := {x := 3.0, y := 4.0}

def distance (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval distance myPoint

inductive SpellSchool where
  | abjuration
  | conjuration
  | divination
  | enchantment
  | evocation
  | illusion
  | necromancy
  | transmutation
deriving Repr, DecidableEq

def schoolDanger : SpellSchool → Nat
  | .abjuration => 1
  | .divination => 2
  | .illusion => 3
  | .transmutation => 4
  | .enchantment => 5
  | .conjuration => 6
  | .evocation => 8
  | .necromancy => 9

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def MyList.length {α : Type} : MyList α → Nat
  | MyList.nil => 0
  | MyList.cons _ tail => 1 + tail.length

def ev : SpellSchool := SpellSchool.evocation
#eval ev
#eval schoolDanger ev
#eval schoolDanger .necromancy

def myNumbers : MyList Nat := .cons 1 (.cons 2 (.cons 3 .nil))
#eval myNumbers.length

def Positive := {n : Nat // n > 0}

def five : Positive := ⟨5, by decide⟩

#eval five
#eval five.val
#check five.property


def NonEmptyList (α : Type) := {xs : List α // xs ≠ []}

def exampleNEL : NonEmptyList Nat :=
  ⟨[1,2,3], by decide⟩

def safeHead {α : Type} [Inhabited α] (nel : NonEmptyList α) : α :=
  match nel.val with
  | x :: _ => x
  -- unreachable
  | [] => default

#eval safeHead exampleNEL

def smallNum : Fin 5 := 3
def anotherSmall : Fin 10 := 7

#eval (smallNum : Fin 5).val

def safeIndex {α : Type} (arr : Array α) (i : Fin arr.size) : α :=
  arr[i]

#eval (3 : Fin 5) + 4 -- (wraps : 7 mod 5 = 2)

def showTwice {α : Type} [ToString α] (x : α) : String :=
  s!"{x} {x}"

#eval showTwice 42
#eval showTwice "hello"
#eval showTwice true

inductive ManaColor where
  | white
  | blue
  | black
  | red
  | green
  | colorless
deriving Repr, DecidableEq

structure ManaCost where
  white : Nat := 0
  blue : Nat := 0
  black : Nat := 0
  red : Nat := 0
  green : Nat := 0
  colorless : Nat := 0
deriving Repr

def ManaCost.total (c : ManaCost) : Nat :=
  c.white + c.blue + c.black + c.red + c.green + c.colorless

structure ManaPool where
  white : Nat := 0
  blue : Nat := 0
  black : Nat := 0
  red : Nat := 0
  green : Nat := 0
  colorless : Nat := 0
deriving Repr

def ManaPool.total (p : ManaPool) : Nat :=
  p.white + p.blue + p.black + p.red + p.green + p.colorless

def ManaPool.canAfford (pool : ManaPool) (cost : ManaCost) : Bool :=
  pool.white ≥ cost.white ∧
  pool.blue ≥ cost.blue ∧
  pool.black ≥ cost.black ∧
  pool.red ≥ cost.red ∧
  pool.green ≥ cost.green ∧
  pool.total ≥ cost.total

def ManaPool.pay (pool : ManaPool) (cost : ManaCost) : Option ManaPool :=
  if pool.canAfford cost then
    some { white := pool.white - cost.white
           blue := pool.blue - cost.blue
           black := pool.black - cost.black
           red := pool.red - cost.red
           green := pool.green - cost.green
           colorless := pool.total - cost.total -
             (pool.white - cost.white) - (pool.blue - cost.blue) -
             (pool.black - cost.black) - (pool.red - cost.red) -
             (pool.green - cost.green) }
  else
    none

inductive CardType where
  | creature (power : Nat) (toughness : Nat)
  | instant
  | sorcery
  | enchantment
  | artifact
deriving Repr

structure Card where
  name : String
  cost : ManaCost
  cardType : CardType
deriving Repr

def goblinGuide : Card :=
  { name := "Goblin Guide"
    cost := { red := 1 }
    cardType := .creature 2 2 }

def searingSpear : Card :=
  { name := "Searing Spear"
    cost := { red := 1, colorless := 1 }
    cardType := .instant }

def dayOfJudgment : Card :=
  { name := "Day of Judgment"
    cost := { white := 2, colorless := 2 }
    cardType := .sorcery }

def swordOfFire : Card :=
  { name := "Sword of Fire and Ice"
    cost := { colorless := 3 }
    cardType := .artifact }

def graveTitan : Card :=
  { name := "Grave Titan"
    cost := { black := 2, colorless := 4 }
    cardType := .creature 6 6 }

def Card.isCreature (c : Card) : Bool :=
  match c.cardType with
  | .creature _ _ => true
  | _ => false

def Card.power (c : Card) : Option Nat :=
  match c.cardType with
  | .creature p _ => some p
  | _ => none

def Card.toughness (c : Card) : Option Nat :=
  match c.cardType with
  | .creature _ t => some t
  | _ => none

structure Creature where
  name : String
  power : Nat
  toughness : Nat
  damage : Nat := 0
deriving Repr

def Creature.fromCard (c : Card) : Option Creature :=
  match c.cardType with
  | .creature p t => some {name := c.name, power := p, toughness := t}
  | _ => none

def Creature.isAlive (c : Creature) : Bool :=
  c.damage < c.toughness

def Creature.takeDamage (c : Creature) (dmg : Nat) : Creature :=
  {c with damage := c.damage + dmg}

def Creature.canBlock (blocker attacker : Creature) : Bool :=
  blocker.isAlive ∧ attacker.isAlive

def combat (attacker blocker : Creature) : Creature × Creature :=
  let attackerAfter := attacker.takeDamage blocker.power
  let blockerAfter := blocker.takeDamage attacker.power
  (attackerAfter, blockerAfter)

abbrev Hand := List Card

def Hand.playable (hand : Hand) (pool : ManaPool) : List Card :=
  hand.filter (λc ↦ pool.canAfford c.cost)

def Hand.creatures (hand : Hand) : List Card :=
  hand.filter Card.isCreature

def Hand.totalCost (hand : Hand) : Nat :=
  hand.foldl (λacc c ↦ acc + c.cost.total) 0
