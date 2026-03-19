example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by grind

example [Lean.Grind.CommRing α] [Lean.Grind.NoNatZeroDivisors α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by grind

example (x y : Fin 11) :
  x ^ 2 * y = 1 →
  x * y ^ 2 = y →
  y * x = 1 := by grind

example (x y : Int) :
    27 ≤ 11 * x + 13 * y →
    11 * x + 13 * y ≤ 45 →
    -10 ≤ 7 * x - 9 * y →
    7 * x - 9 * y ≤ 4 →
    False := by
  grind
