def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

#eval NonTail.sum [1, 2, 3]

def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

-- theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
--   funext xs
--   induction xs with
--   | nil => rfl
--   | cons y ys ih =>
--     simp [NonTail.sum, Tail.sum, Tail.sumHelper]
--     rw [ih]

-- theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
--   n + Tail.sum xs = Tail.sumHelper n xs := by
--   induction xs with
--   | nil => rfl
--   | cons y ys ih =>
--     simp [Tail.sum, Tail.sumHelper]

-- theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
--   (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
--   induction xs with
--   | nil =>
--     intro n
--     rfl
--   | cons y ys ih =>
--     intro n
--     simp [NonTail.sum, Tail.sumHelper]
--     rw [←Nat.add_assoc]

def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar ) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs

-- def BinTree.mirror : BinTree α → BinTree α
--   | .leaf => .leaf
--   | .branch l x r => .branch (mirror r) x (mirror l)

def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1

def Tail.length (xs : List α) : Nat :=
  let rec go (accum : Nat) (xs : List α) :=
    match xs with
    | [] => accum
    | _ :: xs => go (accum + 1) xs
  go 0 xs

#eval Tail.length ([] : List Nat)
#eval Tail.length [1]
#eval Tail.length [1,2]
#eval Tail.length [1,2,3]

def NonTail.factorial : Nat → Nat
  | 0 => 1
  | Nat.succ n => factorial n * (n + 1)

def Tail.factorial (n : Nat) : Nat :=
  let rec go (accum n : Nat) :=
    match n with
    | 0 | 1 => accum
    | n + 1 => go (accum * (n + 1)) (n)
  go 1 n

def NonTail.factorial2 : Nat → Nat
  | 0 => 1
  | Nat.succ n => factorial n * (Nat.succ n)

#eval Tail.factorial 0
#eval Tail.factorial 1
#eval Tail.factorial 2
#eval Tail.factorial 3
#eval Tail.factorial 5
#eval NonTail.factorial2 5

def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs

def Tail.filter (p : α → Bool) (xs : List α) : List α  :=
  let rec go (out xs : List α) :=
    match xs with
    | [] => out
    | x :: xs =>
      if p x then
        go (x :: out) xs
      else
        go out xs
  go [] xs

#eval Tail.filter (· % 2 == 0) [1, 2, 3, 4, 5]
#eval Tail.filter (· % 2 == 1) [1, 2, 3, 4, 5]
