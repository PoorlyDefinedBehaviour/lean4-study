-- https://shaie.ar/posts/verification-in-lean/

def count_from (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | k + 1 => n :: count_from k

#eval count_from 10

def reverse (α : Type) (l : List α) : List α :=
  match l with
  | [] => []
  | x :: xs => reverse α xs ++ [x]

def reverse2 {α : Type} (l : List α) : List α :=
  match l with
  | [] => []
  | x :: xs => reverse2 xs ++ [x]

def sum_of_first_n (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => n + 1 + sum_of_first_n n

#eval sum_of_first_n 4

def my_length {α : Type} (xs : List α) : Nat :=
  let rec go (xs : List α) (length : Nat) :=
    match xs with
    | [] => length
    | _ :: tail => go tail (length  + 1)
  go xs 0

#eval my_length [1, 2, 3] (α := Nat)

def my_append {α : Type} (xs ys : List α) : List α :=
  let rec go accum xs ys :=
    match xs, ys with
    | [], [] => List.reverse accum
    | x :: xs, ys => go (x :: accum) xs ys
    | xs, y :: ys => go (y :: accum) xs ys
  go [] xs ys

#eval my_append [1,2] [3,4]

inductive BinTree (α : Type) [Ord α] where
  | leaf
  | node (left : BinTree α) (value : α) (right : BinTree α)
deriving Repr

def BinTree.count [Ord α] : BinTree α → Nat
  | .leaf => 1
  | .node left _ right =>  left.count + right.count

def BinTree.mirror [Ord α] : BinTree α → BinTree α
  | .leaf => .leaf
  | .node left value right => .node right value left

#eval BinTree.count (.node (.node .leaf 2 .leaf) 1 (.node .leaf 3 .leaf))
#eval BinTree.node (.node .leaf 2 .leaf) 1 (.node .leaf 3 .leaf)
#eval BinTree.mirror (.node (.node .leaf 2 .leaf) 1 (.node .leaf 3 .leaf))

theorem count_from_num (n : Nat) : List.length (count_from n) = n := by
  induction n with
  | zero =>
    unfold count_from
    unfold List.length
    rfl
  | succ p ih =>
    simp [count_from]
    simp [ih]

theorem count_from_num2 (n : Nat) : List.length (count_from n) = n := by
  induction n with
  | zero => simp [count_from]
  | succ p ih => simp [count_from]; exact ih

theorem count_from_num3 (n : Nat) : List.length (count_from n) = n := by
  induction n <;> simp [count_from, *]

theorem reverse_twice_is_id (xs : List α) : List.reverse (List.reverse xs) = xs := by
  sorry
