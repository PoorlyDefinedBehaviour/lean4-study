example (α : Type) (p q : α → Prop) :
  (∀x : α, p x ∧ q x) → ∀y : α, p y :=
  λh ↦
  λy ↦
  show p y from (h y).left

#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u

#check @Eq.refl.{u}

variable (a b c d e : Nat)

theorem T
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg Nat.succ h3
    _ = 1 + d := Nat.add_comm d 1
    _ = e := Eq.symm h4

example : ∃x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz: y < z) : ∃w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro

example : ∃x : Nat, x >0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃y : Nat, y < x :=
  ⟨0, h⟩

variable (α : Type) (p q : α → Prop)

example (h : ∃x, p x ∧ q x) : ∃x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

def IsEven (a : Nat) := ∃b, a = 2 * b

theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
  IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
