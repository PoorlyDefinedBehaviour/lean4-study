open Nat

def sub1: Nat → Nat
  | zero => zero
  | succ n => n

def isZero: Nat → Bool
  | zero => true
  | succ _ => false

example : sub1 0 = 0 := rfl
example (x : Nat) : isZero (succ x) = false := rfl

def swap: α × β → β × α
  | (a, b) => (b, a)

def foo: Nat × Nat → Nat
  | (m, n) => m + n

def bar: Option Nat → Nat
  | none => 0
  | some n => n + 1

def not1: Bool → Bool
  | true => false
  | false => true

theorem not_not : ∀ (b : Bool), not1 (not1 b) = b
  | true => show not1 (not1 true) = true from rfl
  | false => show not (not false) = false from rfl

theorem not_not2 : ∀ (b : Bool), not1 (not1 b) = b := by
  intro b
  cases b with
  | false => rfl
  | true => rfl

theorem not_not3 : ∀ (b : Bool), not1 (not1 b) = b := by
  intro b
  cases b <;> rfl

theorem not_not4 : ∀ (b : Bool), not1 (not1 b) = b := by
  decide

theorem not_not5 : ∀ (b : Bool), not1 (not1 b) = b := by
  intro b
  decide +revert

example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h1 h2 => And.intro h2 h1

example (p q : Prop) : p ∧ q → q ∧ p
  | ⟨p, q⟩ => ⟨q, p⟩

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q

def sub2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | x + 2 => x

example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x + 2) = x := rfl
example : sub2 5 = 3 := rfl

#print sub2

def and : Bool → Bool → Bool
  | true, a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | false, a => a
  | true, _ => true

def cond' : Bool → α → α → α
  | false, _, y => y
  | true, x, _ => x

def tail1 {α : Type u} : List α → List α
  | [] => []
  | _ :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, [] => []
  | α, _ :: as => as

def f1 : Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 2
  | _, _ => default

def foo2 : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _ => 3

#print foo.match_1

section
def add : Nat → Nat → Nat
  | m, zero => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat) : add m zero = m := by
  unfold add
  rfl

theorem add_zero2 (m : Nat) : add m zero = m := by rfl

theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := by rfl

theorem zero_add : ∀ n, add zero n = n
  | zero => rfl
  | succ n => congrArg succ (zero_add n)

def mul : Nat → Nat → Nat
  | _, zero => zero
  | n, succ m => add (mul n m) n
end

def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 =>
      let p := loop n;
      (p.2, p.1 + p.2)

def fibFast2 (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 =>
      let p := loop n
      (p.2, p.1 + p.2)
  (loop n).2

def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0, as => as
    | n + 1, as => loop n (a :: as)
  loop n []

def replicate2 (n : Nat) (a : α) : List α :=
  loop n []
where
  loop
    | 0, as => as
    | n + 1, as => loop n (a :: as)

section
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)
end

def ack : Nat → Nat → Nat
  | 0, y => y + 1
  | x + 1, 0 => ack x 1
  | x + 1, y + 1 => ack x (ack (x + 1) y)

theorem ack_gt_zero : ack n m > 0 := by
  fun_induction ack with
  | case1 y => simp
  | case2 x ih => exact ih
  | case3 x y ih1 ih2 => exact ih2

section
mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n

  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end

example : even (a + 1) = odd a := by
  simp [even]

example : odd (a + 1) = even a := by
  simp [odd]

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a
  induction a with
  | zero => simp [even, odd]
  | succ n ih => simp_all [even, odd]
end

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end

section
open Even Odd

theorem not_odd_zero : ¬ Odd 0 := by
  exact λh ↦ nomatch h
end

inductive Term where
  | const : String → Term
  | app : String → List Term → Term

namespace Term
mutual
  def numConsts : Term → Nat
    | const _ => 1
    | app _ cs => numConstsLst cs
  def numConstsLst : List Term → Nat
    | [] => 0
    | c :: cs => numConsts c + numConstsLst cs
end
end Term
