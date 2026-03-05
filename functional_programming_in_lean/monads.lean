def first (xs : List α) : Option α :=
  xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def firstThird2 (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))

infix:55 " ~~> " => andThen

def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)

-- inductive Except (ε : Type) (α : Type) where
--   | error : ε → Except ε α
--   | ok : α → Except ε α
-- deriving BEq, Hashable, Repr

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length -1})"
  | some x => Except.ok x

#eval get [1,2,3] 3
#eval get [1,2,3] 1

def first2 (xs : List α) : Except String α :=
  get xs 0

def isEven (i : Int) : Bool :=
  i % 2 == 0

def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def andThen2 (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

-- class Monad (m : Type → Type) where
--   pure : α -> m α
--   bind : m α → (α → m β) → m β

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)

-- instance : Monad (State σ) where
--   pure x := fun s => (s, x)
--   bind first next :=
--     fun s =>
--       let (s', x) := first s
--       next x s'

-- def increment (howMuch : Int) : State Int Int :=
--   get >>= fun i =>
--   set (i + howMuch) >>= fun () =>
--   pure i

-- #eval mapM increment [1,2,3,4,5] 0

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Arith where
  | plus
  | minus
  | times
  | div

open Expr
open Arith

def twoPlusThre : Expr Arith :=
  prim plus (const 2) (const 3)

def fourteenDivided : Expr Arith :=
  prim div (const 14)
    (prim minus (const 45)
      (prim times (const 5)
        (const 9)))

def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    match p with
    | Arith.plus => pure (v1 + v2)
    | Arith.minus => pure (v1 - v2)
    | Arith.times => pure (v1 * v2)
    | Arith.div => if v2 == 0 then none else pure (v1 / v2)

def applyPrim : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => if y == 0 then none else pure (x / y)

def evaluateOption2 : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption2 e1 >>= fun v1 =>
    evaluateOption2 e2 >>= fun v2 =>
    applyPrim p v1 v2

def firstThirdFifthSeventh2 [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

def mapM2 [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM f xs
    pure (hd :: tl)

#print Nat
#print Char.isAlpha
#print List.isEmpty
#print IO
#print IO.Error
#print EIO
#print EST
#print EST.Out
#print EST.pure
#print EST.bind

def equal? [BEq α] (x : α) (y : α) : Option α :=
  if x == y then
    some x
  else
    none

def equal2? [BEq α] (x y : α) : Option α :=
  if x == y then
    some x
  else
    none

-- def BinTree.mirror : BinTree α → BinTree α
--   | BinTree.leaf => BinTree.leaf
--   | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)

-- def BinTree.mirror : BinTree α → BinTree α
--   | .leaf => .leaf
  -- | .branch l x r => .branch (mirror r) x (mirror l)

-- def BinTree.Empty : Bintree α := .leaf
-- #check (.empty : BinTree Nat)
