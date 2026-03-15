example (n : Nat) : n ≤ n + 1 := by omega
example (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega
example ( x : Int) (h : x > 0) : x ≥ 1 := by omega

example (a b c : Nat) : a + b + c = c + b + a := by omega
example (n : Nat) : 2 * n = n + n := by omega
example (x y : Int) : x - y + y = x := by omega

example (n : Nat) : 3 * n + 5 * n = 8 * n := by omega
example (x : Int) : 100 * x - 99 * x = x := by omega

example (x y : Int) : 3 * x + 2 * y  = 2 * y + 3 * x := by omega

-- omega doesn't work because there are variables multiplied by variables
-- try ring
-- example (x y : Int) : x * y = y * x := by omega

example (n : Nat) : 100 * n > 99 * n ↔ n > 0 := by omega

example (n : Nat) : n - n = 0 := by omega
example (a b : Nat) : a - b ≤ a := by omega

example (a b : Nat) (h : a ≥ b) : a - b + b = a := by omega

example (a b : Nat) (h : a < b) : a - b = 0 := by omega

example (n : Int) : n - n = 0 := by omega
example (a b : Int) : a - b + b = a := by omega

example (x : Int) (h : x < 0) : x ≤ -1 := by omega
example (a b : Int) : a - b = -(b - a) := by omega

example (n : Nat) : n / 2 ≤ n := by omega
example (n : Nat) (h : n > 1) : n / 2 < n := by omega

example (n : Nat): n % 2 < 2 := by omega
-- example (n m : Nat) (h : m > 0) : n % m < m := by omega

example (n : Nat) : 2 * (n/2) + n % 2 = n := by omega
-- example (n m : Nat) (h : m > 0) : m * (n / m) + n % m = n := by omega

example (n : Nat) (h : n % 2 = 0) : 2 * (n / 2) = n := by omega

def myFun (n : Nat) : Nat :=
  if n < 2 then n
  else myFun (n / 2) + myFun (n / 2)
termination_by n
decreasing_by all_goals omega

example (n : Nat) (h : n ≥ 2) : n / 2 < n := by omega

example (arr : Array Nat) (i : Nat) (h : i < arr.size) : i < arr.size + 1 := by omega
