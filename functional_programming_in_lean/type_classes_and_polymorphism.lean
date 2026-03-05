#check (IO.println)

#check @IO.println

def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents

def List.sumOfContents2 [Add α] [Zero α] : List α → α
  | [] => Zero.zero
  | x :: xs => x + xs.sumOfContents2

def fourNats : List Nat := [1, 2, 3, 4]

#eval fourNats.sumOfContents2

structure PPoint (α : Type) where
  x : α
  y : α

instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | Nat.succ n, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, Nat.succ n => Pos.succ (addPosNat p n)

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

instance : OfNat Pos (Nat.succ n) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | Nat.succ k => Pos.succ (natPlusOne k)
    natPlusOne n


#eval (3 : Pos) + (5 : Nat)

class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)
#eval HPlus.hPlus (3 : Pos) (5 : Nat)

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

#eval HPlus.hPlus (3 : Nat) (5 : Nat)

#check HPlus.hPlus (5 : Nat)

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul := fun p scalar => { x := p.x * scalar, y := p.y * scalar}

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
