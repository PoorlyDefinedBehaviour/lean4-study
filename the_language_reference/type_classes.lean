namespace S
  structure Magma (α : Type u) where
    op: α → α → α

  structure Semigroup (α : Type u) extends Magma α where
    op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

  structure Monoid (α : Type u) extends Semigroup α where
    ident : α
    ident_left : ∀ x, op ident x = x
    ident_right : ∀ x, op x ident = x
end S

namespace C1
  class Monoid (α : Type u) extends S.Semigroup α where
    ident : α
    ident_left : ∀ x, op ident x = x
    ident_right : ∀ x, op x ident = x
end C1

namespace C2
  class Magma (α : Type u) where
    op : α → α → α

  class Semigroup (α : Type U) extends Magma α where
    op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

  class Monoid (α : Type u ) extends Semigroup α where
    ident : α
    ident_left : ∀ x, op ident x = x
    ident_right : ∀ x, op x ident = x
end C2


-- structure Heap (α : Type u) where
--   contents : Array α
-- deriving Repr

-- def Heap.bubbleUp [Ord α] (i : Nat) (xs : Heap α) : Heap α :=
--   if h : i = 0 then xs
--   else if h : i ≥ xs.contents.size then xs
--   else
--     let j := i / 2
--     if Ord.compare xs.contents[i] xs.contents[j] == .lt then
--       Heap.bubbleUp j {xs with contents := xs.contents.swap i j}
--     else
--       xs

-- def Heap.insert [Ord α] (x : α) (xs : Heap α) : Heap α :=
--   let i := xs.contents.size
--   {xs with contents := xs.contents.push x}.bubbleUp i

structure Heap (α : Type u)  [Ord α]where
  contents : Array α

def Heap.bubbleUp [inst : Ord α] (i : Nat) (xs : @Heap α inst) : @Heap α inst :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if inst.compare xs.contents[i] xs.contents[j] == .lt then
      Heap.bubbleUp j {xs with contents := xs.contents.swap i j}
    else
      xs

class abbrev AddMul (α : Type u) := Add α, Mul α

def plusTimes1 [AddMul α] (x y z : α) := x + y * z

class AddMul' (α : Type u) extends Add α, Mul α

def plusTimes2 [AddMul' α] (x y z : α) := x + y * z

#eval plusTimes1 2 5 7
#eval plusTimes2 2 5 7

instance [Add α] [Mul α] : AddMul' α where

#eval plusTimes1 2 5 7

structure NatWrapper where
  val : Nat

instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨λ x y ↦ x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨λ ⟨x⟩ ⟨y⟩ ↦ x == y⟩

#check instBEqNatWrapper

@[instance]
def instBeqNatWrapper : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

inductive NatTree where
  | leaf
  | branch (left : NatTree) (val : Nat) (right : NatTree)

def NatTree.beq : NatTree → NatTree → Bool
    | .leaf, .leaf => true
    | .branch l1 v1 r1, .branch l2 v2 r2 =>
      beq l1 l2 ∧ v1 == v2 ∧ beq r1 r2
    | _, _ => false

instance : BEq NatTree where
  beq := NatTree.beq

instance : BEq NatTree := ⟨NatTree.beq⟩

inductive NatRoseTree where
  | node (val : Nat) (children : Array NatRoseTree)

partial def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    let _ : BEq NatRoseTree := ⟨NatRoseTree.beq⟩
    val1 == val2 ∧ children1 == children2

structure A where
structure B where

deriving instance BEq, Repr for A, B

class IsEnum (α : Type) where
  size : Nat
  toIdx : α → Fin size
  fromIdx : Fin size → α
  to_from_id : ∀ (i : Fin size), toIdx (fromIdx i) = i
  from_to_id : ∀ (x : α), fromIdx (toIdx x) = x

instance : IsEnum Bool where
  size := 2
  toIdx
    | .false => 0
    | .true => 1
  fromIdx
    | 0 => .false
    | 1 => .true
  to_from_id
    | 0 => rfl
    | 1 => rfl
  from_to_id
    | .false => rfl
    | .true => rfl
