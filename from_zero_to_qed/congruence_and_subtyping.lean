def Positive := {n : Nat // n > 0}

def five : Positive := ⟨5, by decide⟩

#eval five
#eval five.val

def NonEmpty (α : Type) := {xs : List α // xs ≠ []}

def singletonList : NonEmpty Nat := ⟨[42], by decide⟩

def doublePositive (p : Positive) : Positive :=
  ⟨p.val * 2, Nat.mul_pos p.property (by decide)⟩

#eval doublePositive ⟨2, by decide⟩

def Even := {n : Nat // n % 2 = 0}
def Odd := {n : Nat // n % 2 = 1}

def zero' : Even := ⟨0, rfl⟩
def two' : Even := ⟨2, rfl⟩
def one' : Odd := ⟨1, rfl⟩
def three' : Odd := ⟨3, rfl⟩

def BoundedNat (lo hi : Nat) := {n : Nat // lo ≤ n ∧ n < hi}

def inRange : BoundedNat 0 10 := ⟨5, by omega⟩

#eval inRange

instance : Coe Positive Nat where
  coe p := p.val

def useAsNat (p : Positive) : Nat := p + 10

#eval useAsNat ⟨5, by decide⟩

instance {α : Type} : Coe (NonEmpty α) (List α) where
  coe xs := xs.val

def listLength (xs : NonEmpty Nat) : Nat := xs.val.length

def listLength' (xs : List Nat) : Nat := xs.length

#eval listLength singletonList
#eval listLength' singletonList

structure Meters where
  val : Float
deriving Repr

structure Kilometers where
  val : Float
deriving Repr

instance : Coe Meters Float where
  coe m := m.val

instance : Coe Kilometers Meters where
  coe km := ⟨km.val * 1000⟩

def addDistance (a : Meters) (b : Kilometers) : Meters :=
  ⟨a.val + (b : Meters).val⟩

#eval addDistance ⟨500⟩ ⟨1.5⟩

instance : CoeFun Positive (λ_ ↦ Nat → Nat) where
  coe p := λn ↦ p.val + n

#eval five 10

structure Adder where
  amount : Nat

instance : CoeFun Adder (λ_ ↦ Nat → Nat) where
  coe a := λn ↦ n + a.amount

def addFive : Adder := ⟨5⟩

#eval addFive 10

structure Predicate' (α : Type) where
  test :α → Bool

instance {α : Type} : CoeFun (Predicate' α) (λ_ ↦ α → Bool) where
  coe p := p.test

def isEven' : Predicate' Nat := ⟨λn ↦ n % 2 == 0⟩

#eval isEven' 4
#eval isEven' 5

example (a b : Nat) (h : a = b) : a + 1 = b + 1:= by congr

example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by congr

example (a b c d : Nat) (h1 : a = b) (h2 : c = d) : a + c = b + d := by
  congr <;> assumption

example (f : Nat → Nat → Nat) (a b c d : Nat) (h1 : a = c) (h2 : b = d) : f a b = f c d := by
  rw [h1, h2]

example (xs ys : List Nat) (h : xs = ys) : xs.length = ys.length := by rw [h]

example (a b : Nat) (h : a = b) : a * a = b * b := by
  subst h
  rfl

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

example (a b : Nat) (h : a = b) (f : Nat → Nat) : f a = f b := by
  -- subst h
  -- rfl
  -- or
  rw [h]

example (n : Nat) : Int := n

def natToInt (n : Nat) : Int := n

#eval natToInt 42

def stringToNat? (s : String) : Option Nat := s.toNat?

#eval stringToNat? "123"
#eval stringToNat? "abc"

def isPositive (n: Int) : Decidable (n > 0) :=
  if h : n > 0 then isTrue h else isFalse h

def checkPositive (n : Int) : String :=
  if n > 0 then "positive" else "not positive"

#eval checkPositive 5
#eval checkPositive (-3)

def decideEqual (a b : Nat) : Decidable (a = b) :=
  if h : a = b then isTrue h else isFalse h

class Animal (α : Type) where
  speak : α → String

class Dog (α : Type) extends Animal α where
  fetch : α → String

structure Labrador where
  name : String

instance : Animal Labrador where
  speak lab := s!"{lab.name} says woof!"

instance : Dog Labrador where
  speak lab := s!"{lab.name} says woof!"
  fetch lab := s!"{lab.name} fetches the ball!"

def makeSpeak {α : Type} [Animal α] (a : α) : String :=
  Animal.speak a

def rex : Labrador := ⟨"Rex"⟩

#eval makeSpeak rex
#eval Dog.fetch rex

structure Shape where
  name : String

structure Circle extends Shape where
  radius : Float

structure Rectangle extends Shape where
  width : Float
  height : Float

def myCircle : Circle := {name := "unit circle", radius := 1.0}
def myRect : Rectangle := {name := "square", width := 2.0, height := 2.0}

#eval myCircle.name
#eval myCircle.radius

structure Meters' where
  val : Float

structure Seconds where
  val : Float

def distance : Meters' := ⟨100.0⟩
def time : Seconds := ⟨10.0⟩

abbrev Speed := Float

def calcSpeed (d : Meters') (t : Seconds) : Speed := d.val / t.val

#eval calcSpeed distance time
