#check Nat
#check String
#check List Nat

#check True
#check true
#check 2 + 2 = 4
#check 2 + 2 == 4

#check 5 = 5
#check 1 + 1 = 2
#check 1 + 1 = 3

#check "hello" = "hello"

#check [1,2] = [1,2]

example : True := trivial

#check False
#check false

example : True → True := λ_ ↦ trivial

example : (1 = 1) → (2 = 2) := λ_ ↦ rfl

-- structure And (α β : Prop) : Prop where
--   left : α
--   right : β

example : True ∧ True := ⟨trivial, trivial⟩

example : (1 = 1) ∧ (2 = 2) := ⟨rfl, rfl⟩

example (h : True ∧ (1 = 1)) : True := h.left

example (h : True ∧ (1 = 1)) : 1 = 1 := h.right

-- inductive Or (α β : Prop) : Prop where
--   | inl : α → Or α β
--   | inr : β → Or α β

example : True ∨ False := Or.inl trivial

example : False ∨ True := Or.inr trivial

example : (1 = 1) ∨ (1 = 2) := Or.inl rfl

#print Not

example : ¬False := λh ↦ h

example : 1 ≠ 2 := by decide

example : ∀ n : Nat, n = n := λ_ ↦ rfl

example : ∀ n : Nat, 0 + n = n := λ_ ↦ rfl

example : ∀ a b : Nat, a + b = b + a := Nat.add_comm

example : ∃ n : Nat, n > 5 := ⟨10, by decide⟩

example : ∃ n : Nat, n + n = 10 := ⟨5, rfl⟩

example : ∃ s : String, s.length = 5 := ⟨"hello", rfl⟩

example (p q : 1 = 1) : p = q := rfl

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  -- ⟨hp, hq⟩
  -- or
  -- by exact ⟨hp, hq⟩
  -- or
  by exact And.intro hp hq
