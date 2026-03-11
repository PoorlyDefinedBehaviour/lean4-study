prefix:max "√"=> λ(n : Nat) ↦ n * n

#eval √5

infix:50 " ⊕ " => λ(a  b : Nat) ↦ a + b + 1

#eval 3 ⊕ 4

postfix:max "!" => λ(n : Nat) ↦ n * n

#eval 5!

notation "⟪" a ", " b "⟫" => (a, b)

notation "if'" c "then'" t "else'" e => if c then t else e

#eval ⟪1, 2⟫

#eval if' true then' 42 else' 0

example : (λ x ↦ x + 1) 2 = 3 := rfl

def myConst := 42
example : myConst = 42 := rfl

example : let x := 5; x + x = 10 := rfl

def dependentTwo (b : Bool) : if b then Unit × Unit else String :=
  match b with
  | true => ((), ())
  | false => "two"

#eval dependentTwo true
#eval dependentTwo false

def boolToType (b : Bool) : Type :=
  if b then Nat else String

def boolExample (b : Bool) : boolToType b :=
  match b with
  | true => (42 : Nat)
  | false => "hello"

def finToString : Fin 3 → String
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"

def double (n : Nat) : Nat := n * 2

def constantFive (_ : Nat) : Nat := 5

def makeVec (n : Nat) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

def dependentPair : (n : Nat) × Fin n := ⟨5, 3⟩

def comp {α β γ : Type} (f : β → γ) (g : α → β) : α → γ := λx ↦ f (g x)



def depComp {α : Type} {β : α → Type} {γ : (x : α) → β x → Type}
    (f : (x : α) → (y : β x) → γ x y)
    (g : (x : α) → β x) :
    (x : α) → γ x (g x) :=
  fun x => f x (g x)

def curriedAdd : Nat → Nat → Nat := λx y ↦ x + y

theorem funext_example (f g : Nat → Nat) (h : ∀x, f x = g x) : f = g :=
  funext h

def add3 (x y z : Nat) : Nat := x + y + z

def add3' : Nat → Nat → Nat → Nat :=
  λx ↦ λy ↦ λz ↦ x + y + z

def add10 : Nat → Nat → Nat := add3 10

def add10And5 : Nat → Nat := add3 10 5

def uncurriedAdd : Nat × Nat → Nat := λp ↦ p.1 + p.2
def curriedVer := Function.curry uncurriedAdd

def addPair := Function.uncurry Nat.add
example : addPair (3, 4) = 7 := rfl

theorem my_funext {α β : Type} (f g : α → β) :
  (∀ x, f x = g x) → f = g := funext

def double' (n : Nat) : Nat := 2 * n
def double'' (n : Nat) : Nat := n + n

theorem doubles_equal : double' = double'' := by
  funext n
  simp [double', double'']
  omega

theorem dep_funext {α : Type} {β : α → Type}
  (f g : (x : α) → β x) :
  (∀ x, f x = g x) → f = g :=
  funext

theorem eta_reduction (f : Nat → Nat) : (λx ↦ f x) = f :=
  funext λ _ ↦ rfl

def addOne : Nat → Nat := λx ↦ x + 1
def succFunc : Nat → Nat := Nat.succ

theorem addOne_eq_suc : addOne = succFunc := by
  funext x
  simp [addOne, succFunc]

def safeDivide (n : Nat) (m : Nat) : Nat :=
  if m = 0 then 0 else n / m

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def gcd (a b : Nat) : Nat :=
  if h : b = 0 then
    a
  else
    have : a % b < b := Nat.mod_lt _ (Nat.pos_of_ne_zero h)
    gcd b (a % b)
-- termination_by
termination_by b

mutual
  def isEvenMut : Nat → Bool
    | 0 => true
    | n +1 => isOddMut n

  def isOddMut : Nat → Bool
    | 0 => false
    | n + 1 => isEvenMut n
end

def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)
termination_by m n => (m,n)

def isInjective {α β : Type} (f : α → β) : Prop :=
  ∀ x y, f x = f y → x = y

theorem and_intro (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

theorem or_elim (P Q R : Prop) (h: P ∨ Q) (hp : P → R) (hq : Q → R) : R :=
  h.elim hp hq

theorem iff_intro (P Q : Prop) (hpq: P → Q) (hqp : Q → P) : P ↔ Q := ⟨hpq, hqp⟩

open Classical in
theorem excluded_middle (P : Prop) : P ∨ ¬P := Classical.em P

instance decidableEven (n : Nat) : Decidable (n % 2 = 0) :=
  if h : n % 2 = 0 then isTrue h else isFalse h

def isEven (n : Nat) : Bool := decide (n % 2 = 0)

example : isEven 4 = true := rfl
example : isEven 5 = false := rfl

theorem subsingleton_prop (P : Prop) : Subsingleton P :=
  ⟨λ _ _ ↦ rfl⟩

inductive Color : Type where
  | red
  | green
  | blue
deriving Repr, DecidableEq

inductive Result (ε α : Type) : Type where
  | ok : α → Result ε α
  | error : ε → Result ε α

structure Point where
  x : Float
  y : Float

inductive Vector' (α : Type) : Nat → Type where
  | nil : Vector' α 0
  | cons : ∀ {n}, α → Vector' α n → Vector' α (n + 1)

def vectorHead {α : Type} {n : Nat} : Vector' α (n + 1) → α
  | Vector'.cons a _ => a

inductive EvenOddList (α : Type) : Bool → Type where
  | nil : EvenOddList α true
  | cons : ∀ {isEven}, α → EvenOddList α isEven → EvenOddList α (¬isEven)

example : Fin 3 := 0
example : Fin 3 := 1
example : Fin 3 := 2
#eval (3 : Fin 3)

def two : Fin 5 := ⟨2, by omega⟩

def safeIndex {α : Type} (arr : Array α) (i : Fin arr.size) α := arr[i]

#eval #[1,2,3]
-- #check safeIndex #[1,2,3] ⟨0, by decide⟩

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

def exampleVec : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))

def Vec.head {α : Type} {n : Nat} : Vec α (n + 1) → α
  | .cons x _ => x

def Vec.tail {α : Type} {n : Nat} : Vec α (n + 1) → Vec α n
  | .cons _ xs => xs

def Vec.map {α β : Type} {n : Nat} (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons x xs => cons (f x) (xs.map f)

inductive Product where
  | HoneyComb
  | SalmonJerky
  | BerryMix
  | GrubBar
  | AcornCrunch
  deriving Repr, DecidableEq

def Product.price : Product → Nat
  | .HoneyComb => 150
  | .SalmonJerky => 200
  | .BerryMix => 100
  | .GrubBar => 125
  | .AcornCrunch => 175

def Product.name : Product → String
  | .HoneyComb => "Honey Comb"
  | .SalmonJerky => "Salmon Jerky"
  | .BerryMix => "Berry Mix"
  | .GrubBar => "Grub Bar"
  | .AcornCrunch => "Acorn Crunch"

structure Machine (cents : Nat) where mk ::

def insertCoin (coin : Nat) {n : Nat} (_m : Machine n) : Machine (n + coin) := ⟨⟩

def insertDollar {n : Nat} (m : Machine n) : Machine (n + 100) := insertCoin 100 m

def vend (p : Product) {n : Nat} (_m : Machine n) (_h : n ≥ p.price) :
  Product × Machine (n - p.price) := (p, ⟨⟩)

def returnChange {n : Nat} (_m : Machine n) : Nat × Machine 0 := (n, ⟨⟩)

def empty : Machine 0 := ⟨⟩

def exampleTransaction : Product × Nat := Id.run do
  let m := empty
  let m := insertDollar m
  let m := insertDollar m
  let (snack, m) := vend .BerryMix m (by native_decide)
  let (change, _) := returnChange m
  return (snack, change)

#eval exampleTransaction
