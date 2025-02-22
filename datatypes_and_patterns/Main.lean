inductive MyBool where
  | false : MyBool
  | true : MyBool

inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

def isZero (n : Nat): Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ k => k

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')
