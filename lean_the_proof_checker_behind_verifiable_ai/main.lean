-- https://codepointer.substack.com/p/lean-the-proof-checker-behind-verifiable

theorem two_plus_two : 2 + 2 = 4 := by rfl

theorem chain (p q r : Prop) : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

theorem chain2 (p q r : Prop) : (p → q) → (q → r) → p → r := by
  intro ptoq qtor p
  exact qtor (ptoq p)

theorem chain3 (p q r : Prop) : (p → q) → (q → r) → p → r := by
  exact λp_to_q ↦ λq_to_r ↦ λp ↦ q_to_r (p_to_q p)

theorem zero_add (n : Nat): 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

#print Nat

def gauss : Nat → Nat
  | 0 => 0
  | n + 1 => gauss n + (n + 1)

theorem gauss_eq (n : Nat) : 2 * gauss n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gauss, Nat.mul_add, ih]
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
