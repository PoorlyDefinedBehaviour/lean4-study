inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

open Plus (plus)

#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
def fourteen : Pos := plus seven seven

#eval fourteen

instance : Add Pos where
  add := Pos.plus

def fourteen2 : Pos := seven + seven

#eval fourteen2

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}"

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

#eval seven * seven

-- class Zero (α : Type) where
--   zero : α

-- class One (α : Type) where
--   one : α

instance : One Pos where
  one := Pos.one

#eval (1 : Pos)

-- class OfNat (α : Type) (_ : Nat) where
--   ofNat : α

inductive LT4 where
  | zero
  | one
  | two
  | three

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)

instance : OfNat Pos (Nat.succ n) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | Nat.succ k => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8
#eval eight

def zero : Pos := 0

structure Pos2 where
  succ ::
  pred : Nat
