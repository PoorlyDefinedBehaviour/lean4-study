inductive Ty where
  | nat : Ty
  | bool : Ty
deriving DecidableEq, Repr

@[reducible] def  Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool

inductive Expr : Ty → Type where
  | nat : Nat → Expr .nat
  | bool : Bool → Expr .bool
  | add : Expr .nat → Expr .nat → Expr .nat
  | mul : Expr .nat → Expr .nat → Expr .nat
  | lt : Expr .nat → Expr .nat → Expr .bool
  | eq : Expr .nat → Expr .nat → Expr .bool
  | and : Expr .bool → Expr .bool → Expr .bool
  | or : Expr .bool → Expr .bool → Expr .bool
  | not : Expr .bool → Expr .bool
  | ite : {t : Ty} → Expr .bool → Expr t → Expr t → Expr t

def Expr.eval : {t : Ty} → Expr t → t.denote
  | _, .nat n => n
  | _, .bool b => b
  | _, .add e1 e2 => e1.eval + e2.eval
  | _, .mul e1 e2 => e1.eval * e2.eval
  | _, .lt e1 e2 => e1.eval < e2.eval
  | _, .eq e1 e2 => e1.eval == e2.eval
  | _, .and e1 e2 => e1.eval ∧ e2.eval
  | _, .or e1 e2 => e1.eval ∨ e2.eval
  | _, .not e => ¬e.eval
  | _, .ite c t e => if c.eval then t.eval else e.eval

def ex1 : Expr .nat := .add (.nat 2) (.nat 3)
def ex2 : Expr .bool := .lt (.nat 2) (.nat 3)
def ex3 : Expr .nat := .ite (.lt (.nat 2) (.nat 3)) (.nat 10) (.nat 20)
def ex4 : Expr .nat := .mul (.add (.nat 2) (.nat 3)) (.nat 4)

#eval ex1.eval
#eval ex2.eval
#eval ex3.eval
#eval ex4.eval

def Expr.constFold : {t : Ty} → Expr t → Expr t
  | _, .nat n => .nat n
  | _, .bool b => .bool b
  | _, .add e1 e2 =>
    match e1.constFold, e2.constFold with
    | .nat n, .nat m => .nat (n + m)
    | e1', e2' => .add e1' e2'
  | _, .mul e1 e2 =>
    match e1.constFold, e2.constFold with
    | .nat n, .nat m => .nat (n * m)
    | e1', e2' => .mul e1' e2'
  | _, .lt e₁ e₂ => .lt e₁.constFold e₂.constFold
  | _, .eq e₁ e₂ => .eq e₁.constFold e₂.constFold
  | _, .and e₁ e₂ => .and e₁.constFold e₂.constFold
  | _, .or e₁ e₂ => .or e₁.constFold e₂.constFold
  | _, .not e => .not e.constFold
  | _, .ite c t e =>
    match c.constFold with
    | .bool true => t.constFold
    | .bool false => e.constFold
    | c' => .ite c' t.constFold e.constFold

theorem constFold_correct : ∀ {t : Ty} (e : Expr t), e.constFold.eval = e.eval := by
  intro t e
  induction e with
  | nat n => rfl
  | bool b => rfl
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.constFold, Expr.eval]
    cases he₁ : e₁.constFold <;> cases he₂ : e₂.constFold <;>
      simp only [Expr.eval, ← ih₁, ← ih₂, he₁, he₂]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.constFold, Expr.eval]
    cases he₁ : e₁.constFold <;> cases he₂ : e₂.constFold <;>
      simp only [Expr.eval, ← ih₁, ← ih₂, he₁, he₂]
  | lt e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | eq e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | and e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | or e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | not e ih => simp only [Expr.constFold, Expr.eval, ih]
  | ite c t e ihc iht ihe =>
    simp only [Expr.constFold, Expr.eval]
    cases hc : c.constFold <;> simp only [Expr.eval, ← ihc, ← iht, ← ihe, hc]
    case bool b => cases b <;> rfl

inductive Expr2 where
  | lit : Nat → Expr2
  | add : Expr2 → Expr2 → Expr2
  | mul : Expr2 → Expr2 → Expr2
deriving Repr

inductive Instr where
  | push : Nat → Instr
  | add : Instr
  | mul : Instr
deriving Repr

def eval : Expr2 → Nat
  | .lit n => n
  | .add a b => eval a + eval b
  | .mul a b => eval a * eval b

def compile : Expr2 → List Instr
  | .lit n => [.push n]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]

def run : List Instr → List Nat → List Nat
  | [], stack => stack
  | .push n :: is, stack => run is (n :: stack)
  | .add :: is, b :: a :: stack => run is ((a + b) :: stack)
  | .mul :: is, b :: a :: stack => run is ((a * b) :: stack)
  | _ :: is, stack => run is stack

theorem run_append (is js : List Instr) (s : List Nat) :
    run (is ++ js) s = run js (run is s) := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    cases i with
    | push n => exact ih _
    | add => cases s with
      | nil => exact ih _
      | cons b s => cases s with
        | nil => exact ih _
        | cons a s => exact ih _
    | mul => cases s with
      | nil => exact ih _
      | cons b s => cases s with
        | nil => exact ih _
        | cons a s => exact ih _

theorem compile_correct (e : Expr2) (s : List Nat) :
  run (compile e) s = eval e :: s := by
  induction e generalizing s with
  | lit n => rfl
  | add a b iha ihb => simp [compile, run_append, iha, ihb, run, eval]
  | mul a b iha ihb => simp [compile, run_append, iha, ihb, run, eval]
