def divide (x y : Nat) : Nat := x / y

def safeDivide (x : Nat) (y : Nat) (h : y ≠ 0) : Nat := x / y

#eval safeDivide 10 2 (by decide)
-- #eval safeDivide 10 0 doesn't compile

theorem example_proof : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl

#check (2 + 2 = 4) -- Prop

#check (∀ n : Nat, n + 0 = n) -- Prop

#check (∃ n : Nat, n > 5) -- Prop

#check (∀ a b c : Nat, (a + b) + c = a + (b + c)) -- Prop

example : 2 + 2 = 4 := rfl

theorem two_plus_two : 2 + 2 = 4 := rfl

#check two_plus_two -- two_plus_two : 2 + 2 = 4

example : ∀ n : Nat, n + 0 = n := λn ↦ Nat.add_zero n

example : ∀ n : Nat, n + 0 = n := by
  intro n -- Let n be any Nat
  rfl     -- This is true by definition

theorem add_example (a b c : Nat) : a + b + c = c + b + a := by
  -- Proof state: ⊢ a + b + c = c + b + a
  omega
   -- Proof state: No goals (proof complete!)

-- theorem add_comm_example : ∀ a b : Nat, a + b = b + a := by
--   intro a b -- Let and b be any Nats
--   -- Goal: a + b = b + a
--   induction a with
--   | zero =>
--     -- Base case: 0 + b = b + 0
--     simp
--   | succ n ih =>
--     -- Inductive case: (n + 1) + b = b + (n + 1)
--     -- ih: n + b = b + n (induction hypothesis)
--     simp [Nat.succ_add, Nat.add_succ]  -- Use known lemmas
--     exact ih          -- Apply induction hypothesis

example : 3 + 4 = 7 := by rfl

example (n : Nat) : n ≤ n + 1 := by omega
