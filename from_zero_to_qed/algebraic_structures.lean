class Semigroup (α : Type) where
  op : α → α → α
  op_assoc : ∀ a b c : α, op (op a b) c = op a (op b c)

class Monoid (α : Type) extends Semigroup α where
  e : α
  e_op : ∀ a : α, op e a = a
  op_e : ∀ a : α, op a e = a

class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_op : ∀ a : α, op (inv a) a = e
  op_inv : ∀ a : α, op a (inv a) = e

variable {G: Type} [Group G]

theorem op_left_cancel (a b c : G) (h : a ⋆ b = a ⋆ c) : b = c := by
  have : a⁻¹ ⋆ (a ⋆ b) = a⁻¹ ⋆ (a ⋆ c) := by rw [h]
  simp only [← Semigroup.op_assoc, Group.inv_op, Monoid.e_op] at this
  exact this

-- Right cancellation: if b ⋆ a = c ⋆ a then b = c
theorem op_right_cancel (a b c : G) (h : b ⋆ a = c ⋆ a) : b = c := by
  have : (b ⋆ a) ⋆ a⁻¹ = (c ⋆ a) ⋆ a⁻¹ := by rw [h]
  simp only [Semigroup.op_assoc, Group.op_inv, Monoid.op_e] at this
  exact this

-- The identity is unique
theorem e_unique (e' : G) (h : ∀ a : G, e' ⋆ a = a) : e' = Monoid.e := by
  have : e' ⋆ Monoid.e = Monoid.e := h Monoid.e
  rw [Monoid.op_e] at this
  exact this

-- Inverses are unique
theorem inv_unique (a b : G) (h : b ⋆ a = Monoid.e) : b = a⁻¹ := by
  have step1 : b ⋆ a ⋆ a⁻¹ = Monoid.e ⋆ a⁻¹ := by rw [h]
  simp only [Semigroup.op_assoc, Group.op_inv, Monoid.op_e, Monoid.e_op] at step1
  exact step1

-- Double inverse: (a⁻¹)⁻¹ = a
theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a := by
  symm
  apply inv_unique
  exact Group.op_inv a

-- Inverse of product: (a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹
theorem op_inv_rev (a b : G) : (a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹ := by
  symm
  apply inv_unique
  calc b⁻¹ ⋆ a⁻¹ ⋆ (a ⋆ b)
      = b⁻¹ ⋆ (a⁻¹ ⋆ (a ⋆ b)) := by rw [Semigroup.op_assoc]
    _ = b⁻¹ ⋆ (a⁻¹ ⋆ a ⋆ b) := by rw [← Semigroup.op_assoc a⁻¹ a b]
    _ = b⁻¹ ⋆ (Monoid.e ⋆ b) := by rw [Group.inv_op]
    _ = b⁻¹ ⋆ b := by rw [Monoid.e_op]
    _ = Monoid.e := Group.inv_op b

inductive Z2 : Type where
  | zero : Z2
  | one : Z2
deriving DecidableEq, Repr

def Z2.add : Z2 → Z2 → Z2
  | .zero, a => a
  | .one, .zero => .one
  | .one, .one => .zero

def Z2.neg : Z2 → Z2
  | a => a

instance : Group Z2 where
  op := Z2.add
  op_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  e := Z2.zero
  e_op := by
    intro a
    cases a <;> rfl
  op_e := by
    intro a
    cases a <;> rfl
  inv := Z2.neg
  inv_op := by
    intro a
    cases a <;> rfl
  op_inv := by
    intro a
    cases a <;> rfl

class CommGroup (α : Type) extends Group α where
  op_comm : ∀ a b : α, Semigroup.op a b = Semigroup.op b a

structure Vec2 where
  x : Int
  y : Int
deriving DecidableEq, Repr

def Vec2.add (v w : Vec2) : Vec2 :=
  ⟨v.x + w.x, v.y + w.y⟩

def Vec2.neg (v : Vec2) : Vec2 :=
  ⟨v.x, -v.y⟩

def Vec2.smul (c : Int) (v : Vec2) : Vec2 :=
  ⟨c * v.x, c * v.y⟩

infixl:65 " ᵥ " => Vec2.add
prefix:100 "-ᵥ" => Vec2.neg
infixl:70 " •ᵥ " => Vec2.smul
