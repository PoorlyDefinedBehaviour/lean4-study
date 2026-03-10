def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_pos : ∀ n, 0 < factorial n := by
  intro n
  induction n with
  | zero => simp [factorial]
  | succ n ih =>
    simp [factorial]
    omega

def safeDiv (n : Nat) (d : Nat) (_ : d ≠ 0) : Nat := n / d

#eval safeDiv 10 3 (by decide)

theorem one_plus_one : 1 + 1 = 2 := by
  rfl

theorem one_plus_one' : 1 + 1 = 2 := rfl

theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem zero_add (n : Nat) : 0 + n = n := by
  simp

theorem two_times_three : 2 * 3 = 6 := by rfl

theorem list_length : [1,2,3].length = 3 := by rfl

theorem string_append : "hello " ++ "world" = "hello world" := by rfl

theorem bool_and : true ∧ false = false := by simp

def double (n : Nat) : Nat := n + n

theorem double_two : double 2 = 4 := by rfl

theorem true_is_true : True := by trivial

theorem one_le_two : 1 ≤ 2 := by trivial

theorem and_true'  : True ∧ True := by trivial

theorem add_zero_simp (n : Nat) : n + 0 = n := by simp

theorem zero_add_simp (n : Nat) : 0 + n = n := by simp

theorem silly_arithmetic : (1 + 0) * (2 + 0) + 0 = 2 := by simp

theorem list_append_nil {α : Type} (xs : List α) : xs ++ [] = xs := by simp

theorem use_hypothesis (a b : Nat) (h : a = b) : a +1 = b + 1 := by simp [h]

theorem exact_demo (P : Prop) (h : P) : P := by exact h

theorem exact_with_function (P Q : Prop) (h : P) (f : P → Q) : Q := by exact f h

theorem imp_self' (P : Prop) : P → P := by
  intro hp
  exact hp

theorem forall_self (P : Nat → Prop) : (∀ n, P n) → (∀ n, P n) := by
  intro h n
  exact h n

theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro hpq hqr hp
  -- exact hqr (hpq hp)
  apply hqr
  apply hpq
  exact hp

theorem have_demo (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  have ab_eq_c : a = c := by rw [h1, h2]
  rw [ab_eq_c, h3]

-- ???
-- theorem sum_square (n : Nat) : (n + 1) * (n + 1) = n *n + 2 * n + 1 := by
--   have expand : (n + 1) * (n + 1) = n * n + n + n + 1 := by ring
--   have simplify : n + n = 2 * n := by ring
--   omega

theorem bool_cases (b : Bool) : b = true ∨ b = false := by
  cases b with
  | true =>
    left
    rfl
  | false =>
    right
    rfl

theorem nat_zero_or_succ (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n with
  | zero =>
    left
    rfl
  | succ m =>
    right
    simp

theorem option_destruct (o : Option Nat) : o = none ∨ ∃ n, o = some n := by
  cases o with
  | none =>
    left
    rfl
  | some n =>
    right
    -- or simp
    exact ⟨n, rfl⟩

theorem sum_twice (n : Nat) : n + n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => omega

theorem length_append {α : Type} (xs ys : List α) :
  (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih]
    omega

theorem omega_simple (n : Nat) (h : n < 10) : n < 100 := by omega

theorem omega_transitive (a b c : Int) (h1 : a < b) (h2 : b < c) : a < c := by omega

theorem omega_sum (x y : Nat) (h : x + y = 10) : x ≤ 10 := by omega

theorem three_lt_five : (3 : Nat) < 5 := by decide

theorem bool_compute : (true ∧ false) = false := by decide

theorem list_membership : 3 ∈ [1,2,3,4,5] := by decide

theorem fin_in_bouds : (2 : Fin 5).val < 5 := by decide

theorem worked_example (n : Nat) : n + 0 = 0 + n := by simp

theorem worked_example2 (a b : Nat) (h : a = b) : a + 1 = b + 1 := by rw [h]

theorem combined_proof (n : Nat) (h : n > 0) : n -1 + 1 = n := by omega

theorem list_nonempty (xs : List Nat) (h : xs ≠ []) : xs.length >0 := by
  cases xs with
  | nil => contradiction
  | cons x xs' => simp

theorem ex_rfl : 3 * 4 = 12 := by rfl

theorem ex_simp (n : Nat) : n * 1 + 0 = n := by simp

theorem ex_intro_exact (P Q : Prop) (h : P) (hpq : P → Q) : Q := by
  exact hpq h

theorem ex_bool_not_not (b : Bool) : ¬¬b = b := by
  cases b <;> simp -- book says rfl

theorem ex_add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero => simp
  | succ n ih => omega

theorem ex_omega (x y : Nat) (h1 : x ≤ 5) (h2 : y ≤ 3) : x + y ≤ 8 := by omega

theorem ex_combined (xs : List Nat) : ([] ++ xs).length = xs.length := by simp

theorem ex_imp_chain (A B C D : Prop) : (A → B) → (B → C) → (C → D) → A → D := by
  intro hab hbc hcd ha
  exact hcd (hbc (hab ha))

theorem ex_nat_lt (n : Nat) : n = 0 ∨ 0 < n := by
  cases n with
  | zero =>
    left
    rfl
  | succ m =>
    right
    omega

theorem ex_reverse_nil : ([] : List Nat).reverse = [] := by rfl

theorem demorgan (P Q : Prop) (h : ¬(P ∧ Q)) : ¬P ∨ ¬Q := by
  by_cases hp : P
  ·
    right
    intro hq
    apply h
    constructor
    · exact hp
    . exact hq
  ·
    left
    exact hp
