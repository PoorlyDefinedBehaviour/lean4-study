-- inductive Bool where
--   | false : Bool
--   | true : Bool

-- inductive Nat where
--   | zero : Nat
--   | succ (n : Nat) : Nat

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 5

#eval pred (Nat.succ 4)

structure Point3D where
  x : Float
  y : Float
  z : Float

def depth (p : Point3D) : Float :=
  match p with
  | {x := h, y := w, z := d} => d

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => even k

def doesntCompile (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (doesntCompile n)

def plus (n k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

def times (n k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

def div (n k : Nat) : Nat :=
  if n < k then
    0
  else
    Nat.succ (div (n - k) k)
