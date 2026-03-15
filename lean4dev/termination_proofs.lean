def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def length : List α → Nat
  | [] => 0
  | _ :: xs => 1 + length xs

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

-- def treeSize : Tree α → Nat
--   | .leaf => 0
--   | .node left _ right => 1 + treeSize left + treeSize right

def gcd (a b : Nat) : Nat :=
  if b = 0 then a
  else gcd b (a % b)
termination_by b

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack (ack (m + 1) n)
termination_by m n => (m, n)

def div (n m : Nat) (h : m > 0) : Nat :=
  if n < m then 0
  else 1 + div (n - m) m h
termination_by n
decreasing_by
  simp_wf
  omega

def search (fuel : Nat) (f : Nat → Bool) (n : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if f n then some n
    else search fuel f (n + 1)
termination_by fuel

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

def f91 (n : Nat) : Nat :=
  if n > 100 then n - 10
  else f91 (f91 (n + 11))

def countdown : Nat → Nat
  | 0 => 0
  | n + 1 => countdown n
-- termination_by n

partial def infiniteLoop : Nat → Nat
  | n => infiniteLoop (n + 1)

def binarySearch (arr : Array Int) (target : Int) (lo hi : Nat) : Option Nat :=
  if lo ≥ hi then none
  else
    let mid := (lo + hi) / 2
    if arr[mid]! < target then binarySearch arr target (mid + 1) hi
    else if arr[mid]! > target then binarySearch arr target lo mid
    else some mid
termination_by hi - lo
decreasing_by all_goals simp_wf; omega

def quickSort : List Nat → List Nat
  | [] => []
  | pivot :: rest =>
    let smaller := rest.filter (· < pivot)
    let larger := rest.filter (· ≥ pivot)
    quickSort smaller ++ [pivot] ++ quickSort larger
termination_by xs => xs.length
